/* -*- Mode: C++; tab-width: 8; indent-tabs-mode: nil; c-basic-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80:
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

/*
 * JavaScript "portable baseline interpreter": an interpreter that is
 * capable of running ICs, but without any native code.
 */

#include "vm/PortableBaselineInterpret.h"

#include "mozilla/Maybe.h"

#include "jsapi.h"

#include "builtin/DataViewObject.h"
#include "builtin/MapObject.h"
#include "jit/BaselineFrame.h"
#include "jit/BaselineIC.h"
#include "jit/BaselineJIT.h"
#include "jit/CacheIR.h"
#include "jit/CacheIRCompiler.h"
#include "jit/CacheIRReader.h"
#include "jit/JitFrames.h"
#include "jit/JitScript.h"
#include "jit/JSJitFrameIter.h"
#include "jit/VMFunctions.h"
#include "vm/AsyncFunction.h"
#include "vm/AsyncIteration.h"
#include "vm/EnvironmentObject.h"
#include "vm/GeneratorObject.h"
#include "vm/Interpreter.h"
#include "vm/Iteration.h"
#include "vm/JitActivation.h"
#include "vm/JSScript.h"
#include "vm/Opcodes.h"
#include "vm/PlainObject.h"
#include "vm/Shape.h"

#include "jit/BaselineFrame-inl.h"
#include "jit/JitScript-inl.h"
#include "vm/EnvironmentObject-inl.h"
#include "vm/Interpreter-inl.h"
#include "vm/JSScript-inl.h"

#define TRACE_INTERP

#ifdef TRACE_INTERP
#  define TRACE_PRINTF(...) \
    do {                    \
      printf(__VA_ARGS__);  \
      fflush(stdout);       \
    } while (0)
#else
#  define TRACE_PRINTF(...) \
    do {                    \
    } while (0)
#endif

using namespace js;
using namespace js::jit;

struct StackVal {
  uint64_t value;

  explicit StackVal(uint64_t v) : value(v) {}
  explicit StackVal(Value v) : value(v.asRawBits()) {}
  explicit StackVal(void* v) : value(reinterpret_cast<uint64_t>(v)) {}

  uint64_t asUInt64() const { return value; }
  Value asValue() const { return Value::fromRawBits(value); }
  void* asVoidPtr() const { return reinterpret_cast<void*>(value); }
  CalleeToken asCalleeToken() const {
    return reinterpret_cast<CalleeToken>(value);
  }
};

struct Stack {
  StackVal* sp;
  StackVal* fp;
  StackVal* base;
  StackVal* top;

  Stack(PortableBaselineStack& pbs)
      : sp(reinterpret_cast<StackVal*>(pbs.top)),
        fp(sp),
        base(reinterpret_cast<StackVal*>(pbs.base)),
        top(reinterpret_cast<StackVal*>(pbs.top)) {}

  [[nodiscard]] StackVal* allocate(size_t size) {
    if (reinterpret_cast<uintptr_t>(base) + size >
        reinterpret_cast<uintptr_t>(sp)) {
      return nullptr;
    }
    sp = reinterpret_cast<StackVal*>(reinterpret_cast<uintptr_t>(sp) - size);
    return sp;
  }

  [[nodiscard]] bool push(StackVal v) {
    if (sp == base) {
      return false;
    }
    *--sp = v;
    return true;
  }
  StackVal pop() {
    MOZ_ASSERT(sp + 1 <= top);
    MOZ_ASSERT(sp < fp);
    return *sp++;
  }
  void popn(size_t len) {
    MOZ_ASSERT(sp + len <= top);
    sp += len;
    MOZ_ASSERT(sp <= fp);
  }

  StackVal* cur() const { return sp; }
  void restore(StackVal* s) { sp = s; }

  uint32_t frameSize(BaselineFrame* curFrame) const {
    return sizeof(StackVal) * (reinterpret_cast<StackVal*>(fp) - cur());
  }

  [[nodiscard]] BaselineFrame* pushFrame(JSContext* cx, JSObject* envChain) {
    TRACE_PRINTF("pushFrame: sp = %p fp = %p\n", sp, fp);
    if (!push(StackVal(fp))) {
      return nullptr;
    }
    fp = cur();
    TRACE_PRINTF("pushFrame: new fp = %p\n", fp);

    BaselineFrame* frame =
        reinterpret_cast<BaselineFrame*>(allocate(BaselineFrame::Size()));
    if (!frame) {
      return nullptr;
    }

    frame->setFlags(BaselineFrame::Flags::RUNNING_IN_INTERPRETER);
    frame->setEnvironmentChain(envChain);
    JSScript* script = frame->script();
    frame->setICScript(script->jitScript()->icScript());
    frame->setInterpreterFields(script->code());
#ifdef DEBUG
    frame->setDebugFrameSize(0);
#endif
    return frame;
  }

  void popFrame(JSContext* cx) {
    StackVal* newTOS = fp + 1;
    fp = reinterpret_cast<StackVal*>(fp->asVoidPtr());
    MOZ_ASSERT(fp);
    TRACE_PRINTF("popFrame: fp = %p\n", fp);
    restore(newTOS);
  }

  [[nodiscard]] StackVal* pushExitFrame(BaselineFrame* prevFrame) {
    uint8_t* prevFP =
        reinterpret_cast<uint8_t*>(prevFrame) + BaselineFrame::Size();
    MOZ_ASSERT(reinterpret_cast<StackVal*>(prevFP) == fp);
#ifdef DEBUG
    MOZ_ASSERT(fp != nullptr);
    uintptr_t frameSize =
        reinterpret_cast<uintptr_t>(fp) - reinterpret_cast<uintptr_t>(cur());
    MOZ_ASSERT(reinterpret_cast<uintptr_t>(fp) >=
               reinterpret_cast<uintptr_t>(cur()));
    TRACE_PRINTF("pushExitFrame: fp = %p cur() = %p -> frameSize = %d\n", fp,
                 cur(), int(frameSize));
    MOZ_ASSERT(frameSize >= BaselineFrame::Size());
    prevFrame->setDebugFrameSize(frameSize);
#endif

    if (!push(StackVal(
            MakeFrameDescriptorForJitCall(FrameType::BaselineJS, 0)))) {
      return nullptr;
    }
    if (!push(StackVal(nullptr))) {  // fake return address.
      return nullptr;
    }
    if (!push(StackVal(prevFP))) {
      return nullptr;
    }
    StackVal* exitFP = cur();
    fp = exitFP;
    TRACE_PRINTF(" -> fp = %p\n", fp);
    if (!push(StackVal(uint64_t(ExitFrameType::Bare)))) {
      return nullptr;
    }
    return exitFP;
  }

  void popExitFrame(StackVal* fp) {
    StackVal* prevFP = reinterpret_cast<StackVal*>(fp->asVoidPtr());
    MOZ_ASSERT(prevFP);
    restore(fp + 3);
    this->fp = prevFP;
    TRACE_PRINTF("popExitFrame: fp -> %p sp -> %p\n", fp, sp);
  }

  BaselineFrame* frameFromFP() {
    return reinterpret_cast<BaselineFrame*>(reinterpret_cast<uintptr_t>(fp) -
                                            BaselineFrame::Size());
  }

  StackVal& operator[](size_t index) { return sp[index]; }
};

struct State {
  RootedValue value0;
  RootedValue value1;
  RootedValue value2;
  RootedValue value3;
  RootedValue res;
  RootedObject obj0;
  RootedObject obj1;
  RootedObject obj2;
  RootedString str0;
  RootedString str1;
  RootedScript script0;
  Rooted<PropertyName*> name0;
  Rooted<jsid> id0;
  Rooted<JSAtom*> atom0;
  RootedFunction fun0;
  Rooted<Scope*> scope0;
  int extraArgs;
  bool spreadCall;

  CacheIRReader cacheIRReader;

  static const int kMaxICVals = 64;
  uint64_t icVals[kMaxICVals];
  uint64_t icResult;

  State(JSContext* cx)
      : value0(cx),
        value1(cx),
        value2(cx),
        value3(cx),
        res(cx),
        obj0(cx),
        obj1(cx),
        obj2(cx),
        str0(cx),
        str1(cx),
        script0(cx),
        name0(cx),
        id0(cx),
        atom0(cx),
        fun0(cx),
        scope0(cx),
        cacheIRReader(nullptr, nullptr) {}
};

class VMFrameManager {
  JSContext* cx;
  BaselineFrame* frame;
  friend class VMFrame;

 public:
  VMFrameManager(JSContext*& cx_, BaselineFrame* frame_)
      : cx(cx_), frame(frame_) {
    // Once the manager exists, we need to create an exit frame to
    // have access to the cx (unless the caller promises it is not
    // calling into the rest of the runtime).
    cx_ = nullptr;
  }

  // Provides the JSContext, but *only* if no calls into the rest of
  // the runtime (that may invoke a GC or stack walk) occur. Avoids
  // the overhead of pushing an exit frame.
  JSContext* cxForLocalUseOnly() const { return cx; }
};

class VMFrame {
  JSContext* cx;
  Stack& stack;
  uint8_t* prevExitFP;
  StackVal* exitFP;
  void* prevSavedStack;

 public:
  VMFrame(VMFrameManager& mgr, Stack& stack_, jsbytecode* pc)
      : cx(mgr.cx), stack(stack_) {
    mgr.frame->interpreterPC() = pc;
    prevExitFP = cx->activation()->asJit()->packedExitFP();
    exitFP = stack.pushExitFrame(mgr.frame);
    if (!exitFP) {
      return;
    }
    cx->activation()->asJit()->setJSExitFP(reinterpret_cast<uint8_t*>(exitFP));
    prevSavedStack = cx->portableBaselineStack().top;
    cx->portableBaselineStack().top = reinterpret_cast<void*>(stack.sp);
  }

  ~VMFrame() {
    cx->activation()->asJit()->setPackedExitFP(prevExitFP);
    stack.popExitFrame(exitFP);
    cx->portableBaselineStack().top = prevSavedStack;
  }

  operator JSContext*() const { return cx; }

  bool success() const { return exitFP != nullptr; }
};

static EnvironmentObject& getEnvironmentFromCoordinate(
    BaselineFrame* frame, EnvironmentCoordinate ec) {
  JSObject* env = &frame->environmentChain()->as<EnvironmentObject>();
  for (unsigned i = ec.hops(); i; i--) {
    env = &env->as<EnvironmentObject>().enclosingEnvironment();
  }
  return env->as<EnvironmentObject>();
}

static bool PortableBaselineInterpret(JSContext* cx_, Stack& stack,
                                      JSObject* envChain, Value* ret);

#define TRY(x)    \
  if (!(x)) {     \
    return false; \
  }

#define PUSH(val) TRY(stack.push(val));

#define PUSH_EXIT_FRAME_OR_RET(value) \
  VMFrame cx(frameMgr, stack, pc);    \
  if (!cx.success()) {                \
    return value;                     \
  }

enum class ICInterpretOpResult {
  NextIC,
  Ok,
  Return,
  Error,
};

#define PUSH_IC_FRAME()                               \
  PUSH_EXIT_FRAME_OR_RET(ICInterpretOpResult::Error); \
  stack[0] = StackVal(cstub);

static ICInterpretOpResult MOZ_ALWAYS_INLINE
ICInterpretOp(BaselineFrame* frame, VMFrameManager& frameMgr, Stack& stack,
              State& state, ICCacheIRStub* cstub, jsbytecode* pc) {
  CacheOp op = state.cacheIRReader.readOp();
  switch (op) {
    case CacheOp::ReturnFromIC:
      TRACE_PRINTF("stub successful!\n");
      return ICInterpretOpResult::Return;

    case CacheOp::GuardToInt32: {
      ValOperandId inputId = state.cacheIRReader.valOperandId();
      Value v = Value::fromRawBits(state.icVals[inputId.id()]);
      TRACE_PRINTF("GuardToInt32 (%d): icVal %" PRIx64 "\n", inputId.id(),
                   state.icVals[inputId.id()]);
      if (!v.isInt32()) {
        return ICInterpretOpResult::NextIC;
      }
      // N.B.: we don't need to unbox because the low 32 bits are
      // already the int32 itself, and we are careful when using
      // `Int32Operand`s to only use those bits.
      break;
    }

    case CacheOp::GuardToObject: {
      ValOperandId inputId = state.cacheIRReader.valOperandId();
      Value v = Value::fromRawBits(state.icVals[inputId.id()]);
      TRACE_PRINTF("GuardToObject: icVal %" PRIx64 "\n",
                   state.icVals[inputId.id()]);
      if (!v.isObject()) {
        return ICInterpretOpResult::NextIC;
      }
      state.icVals[inputId.id()] = reinterpret_cast<uint64_t>(&v.toObject());
      break;
    }

    case CacheOp::GuardToString: {
      TRACE_PRINTF("GuardToString\n");
      ValOperandId inputId = state.cacheIRReader.valOperandId();
      Value v = Value::fromRawBits(state.icVals[inputId.id()]);
      if (!v.isString()) {
        return ICInterpretOpResult::NextIC;
      }
      state.icVals[inputId.id()] = reinterpret_cast<uint64_t>(v.toString());
      break;
    }

    case CacheOp::GuardToSymbol: {
      TRACE_PRINTF("GuardToSymbol\n");
      ValOperandId inputId = state.cacheIRReader.valOperandId();
      Value v = Value::fromRawBits(state.icVals[inputId.id()]);
      if (!v.isSymbol()) {
        return ICInterpretOpResult::NextIC;
      }
      state.icVals[inputId.id()] = reinterpret_cast<uint64_t>(v.toSymbol());
      break;
    }

    case CacheOp::GuardToBigInt: {
      TRACE_PRINTF("GuardToBigInt\n");
      ValOperandId inputId = state.cacheIRReader.valOperandId();
      Value v = Value::fromRawBits(state.icVals[inputId.id()]);
      if (!v.isBigInt()) {
        return ICInterpretOpResult::NextIC;
      }
      state.icVals[inputId.id()] = reinterpret_cast<uint64_t>(v.toBigInt());
      break;
    }

    case CacheOp::GuardToBoolean: {
      TRACE_PRINTF("GuardToBoolean\n");
      ValOperandId inputId = state.cacheIRReader.valOperandId();
      Value v = Value::fromRawBits(state.icVals[inputId.id()]);
      if (!v.isBoolean()) {
        return ICInterpretOpResult::NextIC;
      }
      state.icVals[inputId.id()] = v.toBoolean() ? 1 : 0;
      break;
    }

    case CacheOp::GuardIsNullOrUndefined: {
      TRACE_PRINTF("GuardIsNullOrUndefined\n");
      ObjOperandId inputId = state.cacheIRReader.objOperandId();
      Value v = Value::fromRawBits(state.icVals[inputId.id()]);
      if (!v.isNullOrUndefined()) {
        return ICInterpretOpResult::NextIC;
      }
      break;
    }

    case CacheOp::GuardIsNull: {
      TRACE_PRINTF("GuardIsNull\n");
      ObjOperandId inputId = state.cacheIRReader.objOperandId();
      Value v = Value::fromRawBits(state.icVals[inputId.id()]);
      if (!v.isNull()) {
        return ICInterpretOpResult::NextIC;
      }
      break;
    }

    case CacheOp::GuardIsUndefined: {
      TRACE_PRINTF("GuardIsUndefined\n");
      ObjOperandId inputId = state.cacheIRReader.objOperandId();
      Value v = Value::fromRawBits(state.icVals[inputId.id()]);
      if (!v.isUndefined()) {
        return ICInterpretOpResult::NextIC;
      }
      break;
    }

    case CacheOp::GuardNonDoubleType: {
      TRACE_PRINTF("GuardNonDoubleType\n");
      ValOperandId inputId = state.cacheIRReader.valOperandId();
      ValueType type = state.cacheIRReader.valueType();
      Value val = Value::fromRawBits(state.icVals[inputId.id()]);
      switch (type) {
        case ValueType::String:
          if (!val.isString()) {
            return ICInterpretOpResult::NextIC;
          }
          break;
        case ValueType::Symbol:
          if (!val.isSymbol()) {
            return ICInterpretOpResult::NextIC;
          }
          break;
        case ValueType::BigInt:
          if (!val.isBigInt()) {
            return ICInterpretOpResult::NextIC;
          }
          break;
        case ValueType::Int32:
          if (!val.isInt32()) {
            return ICInterpretOpResult::NextIC;
          }
          break;
        case ValueType::Boolean:
          if (!val.isBoolean()) {
            return ICInterpretOpResult::NextIC;
          }
          break;
        case ValueType::Undefined:
          if (!val.isUndefined()) {
            return ICInterpretOpResult::NextIC;
          }
          break;
        case ValueType::Null:
          if (!val.isNull()) {
            return ICInterpretOpResult::NextIC;
          }
          break;
        default:
          MOZ_CRASH("Unexpected type");
      }
      break;
    }

    case CacheOp::GuardShape: {
      TRACE_PRINTF("GuardShape\n");
      ObjOperandId objId = state.cacheIRReader.objOperandId();
      uint32_t shapeOffset = state.cacheIRReader.stubOffset();
      NativeObject* nobj =
          reinterpret_cast<NativeObject*>(state.icVals[objId.id()]);
      uintptr_t expectedShape =
          cstub->stubInfo()->getStubRawWord(cstub, shapeOffset);
      if (reinterpret_cast<uintptr_t>(nobj->shape()) != expectedShape) {
        return ICInterpretOpResult::NextIC;
      }
      break;
    }

    case CacheOp::GuardProto: {
      TRACE_PRINTF("GuardProto\n");
      ObjOperandId objId = state.cacheIRReader.objOperandId();
      uint32_t protoOffset = state.cacheIRReader.stubOffset();
      NativeObject* nobj =
          reinterpret_cast<NativeObject*>(state.icVals[objId.id()]);
      uintptr_t expectedProto =
          cstub->stubInfo()->getStubRawWord(cstub, protoOffset);
      if (reinterpret_cast<uintptr_t>(nobj->staticPrototype()) !=
          expectedProto) {
        return ICInterpretOpResult::NextIC;
      }
      break;
    }

    case CacheOp::LoadProto: {
      TRACE_PRINTF("LoadProto\n");
      ObjOperandId objId = state.cacheIRReader.objOperandId();
      ObjOperandId resultId = state.cacheIRReader.objOperandId();
      NativeObject* nobj =
          reinterpret_cast<NativeObject*>(state.icVals[objId.id()]);
      state.icVals[resultId.id()] =
          reinterpret_cast<uintptr_t>(nobj->staticPrototype());
      break;
    }

    case CacheOp::GuardSpecificFunction: {
      TRACE_PRINTF("GuardSpecificFunction\n");
      ObjOperandId funId = state.cacheIRReader.objOperandId();
      uint32_t expectedOffset = state.cacheIRReader.stubOffset();
      uint32_t nargsAndFlagsOffset = state.cacheIRReader.stubOffset();
      (void)nargsAndFlagsOffset;  // Unused.
      uintptr_t expected =
          cstub->stubInfo()->getStubRawWord(cstub, expectedOffset);
      if (expected != state.icVals[funId.id()]) {
        return ICInterpretOpResult::NextIC;
      }
      break;
    }

    case CacheOp::GuardSpecificObject: {
      TRACE_PRINTF("GuardSpecificObject\n");
      ObjOperandId funId = state.cacheIRReader.objOperandId();
      uint32_t expectedOffset = state.cacheIRReader.stubOffset();
      uintptr_t expected =
          cstub->stubInfo()->getStubRawWord(cstub, expectedOffset);
      if (expected != state.icVals[funId.id()]) {
        return ICInterpretOpResult::NextIC;
      }
      break;
    }

    case CacheOp::GuardSpecificAtom: {
      TRACE_PRINTF("GuardSpecificAtom\n");
      StringOperandId strId = state.cacheIRReader.stringOperandId();
      uint32_t expectedOffset = state.cacheIRReader.stubOffset();
      uintptr_t expected =
          cstub->stubInfo()->getStubRawWord(cstub, expectedOffset);
      if (expected != state.icVals[strId.id()]) {
        return ICInterpretOpResult::NextIC;
      }
      break;
    }

    case CacheOp::GuardSpecificSymbol: {
      TRACE_PRINTF("GuardSpecificSymbol\n");
      SymbolOperandId symId = state.cacheIRReader.symbolOperandId();
      uint32_t expectedOffset = state.cacheIRReader.stubOffset();
      uintptr_t expected =
          cstub->stubInfo()->getStubRawWord(cstub, expectedOffset);
      if (expected != state.icVals[symId.id()]) {
        return ICInterpretOpResult::NextIC;
      }
      break;
    }

    case CacheOp::GuardSpecificInt32: {
      TRACE_PRINTF("GuardSpecificInt32\n");
      Int32OperandId int32Id = state.cacheIRReader.int32OperandId();
      uint32_t expectedOffset = state.cacheIRReader.stubOffset();
      uint32_t expected =
          cstub->stubInfo()->getStubRawInt32(cstub, expectedOffset);
      if (expected != uint32_t(state.icVals[int32Id.id()])) {
        return ICInterpretOpResult::NextIC;
      }
      break;
    }

    case CacheOp::GuardClass: {
      TRACE_PRINTF("GuardClass\n");
      ObjOperandId objId = state.cacheIRReader.objOperandId();
      GuardClassKind kind = state.cacheIRReader.guardClassKind();
      JSObject* object = reinterpret_cast<JSObject*>(state.icVals[objId.id()]);
      switch (kind) {
        case GuardClassKind::Array:
          if (object->getClass() != &ArrayObject::class_) {
            return ICInterpretOpResult::NextIC;
          }
          break;
        case GuardClassKind::PlainObject:
          if (object->getClass() != &PlainObject::class_) {
            return ICInterpretOpResult::NextIC;
          }
          break;
        case GuardClassKind::ArrayBuffer:
          if (object->getClass() != &ArrayBufferObject::class_) {
            return ICInterpretOpResult::NextIC;
          }
          break;
        case GuardClassKind::SharedArrayBuffer:
          if (object->getClass() != &SharedArrayBufferObject::class_) {
            return ICInterpretOpResult::NextIC;
          }
          break;
        case GuardClassKind::DataView:
          if (object->getClass() != &DataViewObject::class_) {
            return ICInterpretOpResult::NextIC;
          }
          break;
        case GuardClassKind::MappedArguments:
          if (object->getClass() != &MappedArgumentsObject::class_) {
            return ICInterpretOpResult::NextIC;
          }
          break;
        case GuardClassKind::UnmappedArguments:
          if (object->getClass() != &UnmappedArgumentsObject::class_) {
            return ICInterpretOpResult::NextIC;
          }
          break;
        case GuardClassKind::WindowProxy:
          if (object->getClass() != frameMgr.cxForLocalUseOnly()
                                        ->runtime()
                                        ->maybeWindowProxyClass()) {
            return ICInterpretOpResult::NextIC;
          }
          break;
        case GuardClassKind::JSFunction:
          if (!object->is<JSFunction>()) {
            return ICInterpretOpResult::NextIC;
          }
          break;
        case GuardClassKind::Set:
          if (object->getClass() != &SetObject::class_) {
            return ICInterpretOpResult::NextIC;
          }
          break;
        case GuardClassKind::Map:
          if (object->getClass() != &MapObject::class_) {
            return ICInterpretOpResult::NextIC;
          }
          break;
        case GuardClassKind::BoundFunction:
          if (object->getClass() != &BoundFunctionObject::class_) {
            return ICInterpretOpResult::NextIC;
          }
          break;
      }
      break;
    }

    case CacheOp::StoreDynamicSlot: {
      TRACE_PRINTF("StoreDynamicSlot\n");
      ObjOperandId objId = state.cacheIRReader.objOperandId();
      uint32_t offsetOffset = state.cacheIRReader.stubOffset();
      uint32_t offset = cstub->stubInfo()->getStubRawInt32(cstub, offsetOffset);
      ValOperandId valId = state.cacheIRReader.valOperandId();
      NativeObject* nobj =
          reinterpret_cast<NativeObject*>(state.icVals[objId.id()]);
      HeapSlot* slots = nobj->getSlotsUnchecked();
      Value val = Value::fromRawBits(state.icVals[valId.id()]);
      size_t dynSlot = offset / sizeof(Value);
      size_t slot = dynSlot + nobj->numFixedSlots();
      slots[dynSlot].set(nobj, HeapSlot::Slot, slot, val);
      break;
    }

    case CacheOp::LoadObject: {
      TRACE_PRINTF("LoadObject\n");
      ObjOperandId objId = state.cacheIRReader.objOperandId();
      uint32_t objOffset = state.cacheIRReader.stubOffset();
      intptr_t obj = cstub->stubInfo()->getStubRawWord(cstub, objOffset);
      state.icVals[objId.id()] = obj;
      break;
    }

    case CacheOp::LoadOperandResult: {
      TRACE_PRINTF("LoadOperandResult\n");
      ValOperandId valId = state.cacheIRReader.valOperandId();
      state.icResult = state.icVals[valId.id()];
      break;
    }

    case CacheOp::LoadValueResult: {
      TRACE_PRINTF("LoadValueResult\n");
      uint32_t valOffset = state.cacheIRReader.stubOffset();
      state.icResult = cstub->stubInfo()->getStubRawInt64(cstub, valOffset);
      break;
    }

    case CacheOp::LoadObjectResult: {
      TRACE_PRINTF("LoadObjectResult\n");
      ObjOperandId objId = state.cacheIRReader.objOperandId();
      state.icResult =
          ObjectValue(*reinterpret_cast<JSObject*>(state.icVals[objId.id()]))
              .asRawBits();
      break;
    }

    case CacheOp::LoadStringResult: {
      TRACE_PRINTF("LoadStringResult\n");
      StringOperandId stringId = state.cacheIRReader.stringOperandId();
      state.icResult =
          StringValue(reinterpret_cast<JSString*>(state.icVals[stringId.id()]))
              .asRawBits();
      break;
    }

    case CacheOp::LoadConstantStringResult: {
      TRACE_PRINTF("LoadConstantStringResult\n");
      uint32_t offset = state.cacheIRReader.stubOffset();
      JSString* str = reinterpret_cast<JSString*>(
          cstub->stubInfo()->getStubRawWord(cstub, offset));
      state.icResult = StringValue(str).asRawBits();
      break;
    }

    case CacheOp::LoadSymbolResult: {
      TRACE_PRINTF("LoadSymbolResult\n");
      SymbolOperandId symbolId = state.cacheIRReader.symbolOperandId();
      state.icResult = SymbolValue(reinterpret_cast<JS::Symbol*>(
                                       state.icVals[symbolId.id()]))
                           .asRawBits();
      break;
    }

    case CacheOp::LoadInt32Result: {
      TRACE_PRINTF("LoadInt32Result\n");
      Int32OperandId intId = state.cacheIRReader.int32OperandId();
      state.icResult = Int32Value(state.icVals[intId.id()]).asRawBits();
      break;
    }

    case CacheOp::LoadBigIntResult: {
      TRACE_PRINTF("LoadBigIntResult\n");
      BigIntOperandId bigintId = state.cacheIRReader.bigIntOperandId();
      state.icResult = BigIntValue(reinterpret_cast<JS::BigInt*>(
                                       state.icVals[bigintId.id()]))
                           .asRawBits();
      break;
    }

    case CacheOp::LoadDoubleResult: {
      TRACE_PRINTF("LoadDoubleResult\n");
      NumberOperandId numId = state.cacheIRReader.numberOperandId();
      Value val = Value::fromRawBits(state.icVals[numId.id()]);
      if (val.isInt32()) {
        val = DoubleValue(val.toInt32());
      }
      state.icResult = val.asRawBits();
      break;
    }

    case CacheOp::LoadBooleanResult: {
      TRACE_PRINTF("LoadBooleanResult\n");
      state.icResult = BooleanValue(state.cacheIRReader.readBool()).asRawBits();
      break;
    }

    case CacheOp::LoadFixedSlotResult: {
      TRACE_PRINTF("LoadFixedSlotResult\n");
      ObjOperandId objId = state.cacheIRReader.objOperandId();
      uint32_t offsetOffset = state.cacheIRReader.stubOffset();
      uintptr_t offset =
          cstub->stubInfo()->getStubRawInt32(cstub, offsetOffset);
      NativeObject* nobj =
          reinterpret_cast<NativeObject*>(state.icVals[objId.id()]);
      Value* slot =
          reinterpret_cast<Value*>(reinterpret_cast<uintptr_t>(nobj) + offset);
      TRACE_PRINTF(
          "LoadFixedSlotResult: obj %p offsetOffset %d offset %d slotPtr %p "
          "slot %" PRIx64 "\n",
          nobj, int(offsetOffset), int(offset), slot, slot->asRawBits());
      state.icResult = slot->asRawBits();
      break;
    }

    case CacheOp::LoadDynamicSlotResult: {
      TRACE_PRINTF("LoadDynamicSlotResult\n");
      ObjOperandId objId = state.cacheIRReader.objOperandId();
      uint32_t offsetOffset = state.cacheIRReader.stubOffset();
      uintptr_t offset =
          cstub->stubInfo()->getStubRawInt32(cstub, offsetOffset);
      NativeObject* nobj =
          reinterpret_cast<NativeObject*>(state.icVals[objId.id()]);
      HeapSlot* slots = nobj->getSlotsUnchecked();
      state.icResult = slots[offset / sizeof(Value)].get().asRawBits();
      break;
    }

    case CacheOp::LoadArgumentDynamicSlot: {
      TRACE_PRINTF("LoadArgumentDynamicSlot\n");
      ValOperandId resultId = state.cacheIRReader.valOperandId();
      Int32OperandId argcId = state.cacheIRReader.int32OperandId();
      uint8_t slotIndex = state.cacheIRReader.readByte();
      int32_t argc = int32_t(state.icVals[argcId.id()]);
      Value val = stack[slotIndex + argc].asValue();
      state.icVals[resultId.id()] = val.asRawBits();
      break;
    }

    case CacheOp::LoadArgumentFixedSlot: {
      TRACE_PRINTF("LoadArgumentFixedSlot\n");
      ValOperandId resultId = state.cacheIRReader.valOperandId();
      uint8_t slotIndex = state.cacheIRReader.readByte();
      Value val = stack[slotIndex].asValue();
      TRACE_PRINTF(" -> slot %d: val %" PRIx64 "\n", int(slotIndex),
                   val.asRawBits());
      state.icVals[resultId.id()] = val.asRawBits();
      break;
    }

#define INT32_OP(name, op, extra_check)                          \
  case CacheOp::Int32##name##Result: {                           \
    TRACE_PRINTF("Int32" #name "Result\n");                      \
    Int32OperandId lhsId = state.cacheIRReader.int32OperandId(); \
    Int32OperandId rhsId = state.cacheIRReader.int32OperandId(); \
    int64_t lhs = int64_t(int32_t(state.icVals[lhsId.id()]));    \
    int64_t rhs = int64_t(int32_t(state.icVals[rhsId.id()]));    \
    extra_check;                                                 \
    int64_t result = lhs op rhs;                                 \
    if (result < INT32_MIN || result > INT32_MAX) {              \
      return ICInterpretOpResult::NextIC;                        \
    }                                                            \
    state.icResult = Int32Value(int32_t(result)).asRawBits();    \
    break;                                                       \
  }

      INT32_OP(Add, +, {});
      INT32_OP(Sub, -, {});
      INT32_OP(Mul, *, {});
      INT32_OP(Div, /, {
        if (rhs == 0) {
          return ICInterpretOpResult::NextIC;
        }
      });
      INT32_OP(Mod, %, {
        if (rhs == 0) {
          return ICInterpretOpResult::NextIC;
        }
      });
      INT32_OP(Pow, <<, {
        if (rhs >= 32 || rhs < 0) {
          return ICInterpretOpResult::NextIC;
        }
      });

    case CacheOp::Int32IncResult: {
      TRACE_PRINTF("Int32IncResult\n");
      Int32OperandId intId = state.cacheIRReader.int32OperandId();
      int64_t value = int64_t(int32_t(state.icVals[intId.id()]));
      value++;
      if (value > INT32_MAX) {
        return ICInterpretOpResult::NextIC;
      }
      state.icResult = Int32Value(int32_t(value)).asRawBits();
      break;
    }

    case CacheOp::CompareInt32Result: {
      TRACE_PRINTF("CompareInt32Result\n");
      JSOp op = state.cacheIRReader.jsop();
      Int32OperandId lhsId = state.cacheIRReader.int32OperandId();
      Int32OperandId rhsId = state.cacheIRReader.int32OperandId();
      int64_t lhs = int64_t(int32_t(state.icVals[lhsId.id()]));
      int64_t rhs = int64_t(int32_t(state.icVals[rhsId.id()]));
      TRACE_PRINTF("lhs (%d) = %" PRIi64 " rhs (%d) = %" PRIi64 "\n",
                   lhsId.id(), lhs, rhsId.id(), rhs);
      bool result;
      switch (op) {
        case JSOp::Eq:
        case JSOp::StrictEq:
          result = lhs == rhs;
          break;
        case JSOp::Ne:
        case JSOp::StrictNe:
          result = lhs != rhs;
          break;
        case JSOp::Lt:
          result = lhs < rhs;
          break;
        case JSOp::Le:
          result = lhs <= rhs;
          break;
        case JSOp::Gt:
          result = lhs > rhs;
          break;
        case JSOp::Ge:
          result = lhs >= rhs;
          break;
        default:
          MOZ_CRASH("Unexpected opcode");
      }
      state.icResult = BooleanValue(result).asRawBits();
      break;
    }

    case CacheOp::CompareStringResult: {
      TRACE_PRINTF("CompareStringResult\n");
      JSOp op = state.cacheIRReader.jsop();
      StringOperandId lhsId = state.cacheIRReader.stringOperandId();
      StringOperandId rhsId = state.cacheIRReader.stringOperandId();
      state.str0 = reinterpret_cast<JSString*>(state.icVals[lhsId.id()]);
      state.str1 = reinterpret_cast<JSString*>(state.icVals[rhsId.id()]);
      {
        PUSH_IC_FRAME();
        bool result;
        switch (op) {
          case JSOp::Eq:
          case JSOp::StrictEq:
            if (!StringsEqual<EqualityKind::Equal>(cx, state.str0, state.str1,
                                                   &result)) {
              return ICInterpretOpResult::Error;
            }
            break;
          case JSOp::Ne:
          case JSOp::StrictNe:
            if (!StringsEqual<EqualityKind::NotEqual>(cx, state.str0,
                                                      state.str1, &result)) {
              return ICInterpretOpResult::Error;
            }
            break;
          case JSOp::Lt:
            if (!StringsCompare<ComparisonKind::LessThan>(
                    cx, state.str0, state.str1, &result)) {
              return ICInterpretOpResult::Error;
            }
            break;
          case JSOp::Ge:
            if (!StringsCompare<ComparisonKind::GreaterThanOrEqual>(
                    cx, state.str0, state.str1, &result)) {
              return ICInterpretOpResult::Error;
            }
            break;
          case JSOp::Le:
            if (!StringsCompare<ComparisonKind::GreaterThanOrEqual>(
                    cx, state.str1, state.str0, &result)) {
              return ICInterpretOpResult::Error;
            }
            break;
          case JSOp::Gt:
            if (!StringsCompare<ComparisonKind::LessThan>(
                    cx, state.str1, state.str0, &result)) {
              return ICInterpretOpResult::Error;
            }
            break;
          default:
            MOZ_CRASH("bad opcode");
        }
        state.icResult = BooleanValue(result).asRawBits();
      }
      break;
    }

    case CacheOp::GuardGlobalGeneration: {
      TRACE_PRINTF("GuardFunctionScript\n");
      uint32_t expectedOffset = state.cacheIRReader.stubOffset();
      uint32_t generationAddrOffset = state.cacheIRReader.stubOffset();
      uint32_t expected =
          cstub->stubInfo()->getStubRawInt32(cstub, expectedOffset);
      uint32_t* generationAddr = reinterpret_cast<uint32_t*>(
          cstub->stubInfo()->getStubRawWord(cstub, generationAddrOffset));
      if (*generationAddr != expected) {
        return ICInterpretOpResult::NextIC;
      }
      break;
    }

    case CacheOp::GuardFunctionScript: {
      TRACE_PRINTF("GuardFunctionScript\n");
      ObjOperandId funId = state.cacheIRReader.objOperandId();
      JSFunction* fun = reinterpret_cast<JSFunction*>(state.icVals[funId.id()]);
      uint32_t expectedOffset = state.cacheIRReader.stubOffset();
      BaseScript* expected = reinterpret_cast<BaseScript*>(
          cstub->stubInfo()->getStubRawWord(cstub, expectedOffset));
      uint32_t nargsFlagsAndOffset = state.cacheIRReader.stubOffset();
      (void)nargsFlagsAndOffset;

      if (!fun->hasBaseScript() || fun->baseScript() != expected) {
        return ICInterpretOpResult::NextIC;
      }

      break;
    }

    case CacheOp::CallScriptedFunction:
    case CacheOp::CallNativeFunction: {
      bool isNative = op == CacheOp::CallNativeFunction;
      TRACE_PRINTF("CallScriptedFunction / CallNativeFunction (native: %d)\n",
                   isNative);
      ObjOperandId calleeId = state.cacheIRReader.objOperandId();
      JSFunction* callee =
          reinterpret_cast<JSFunction*>(state.icVals[calleeId.id()]);
      Int32OperandId argcId = state.cacheIRReader.int32OperandId();
      uint32_t argc = uint32_t(state.icVals[argcId.id()]);
      CallFlags flags = state.cacheIRReader.callFlags();
      uint32_t argcFixed = state.cacheIRReader.uint32Immediate();
      (void)argcFixed;
      bool ignoresRv = false;
      if (isNative) {
        ignoresRv = state.cacheIRReader.readBool();
      }

      // For now, fail any constructing or different-realm cases.
      if (flags.isConstructing() || !flags.isSameRealm()) {
        TRACE_PRINTF("failing: constructing or not same realm\n");
        return ICInterpretOpResult::NextIC;
      }
      // And support only "standard" arg formats.
      if (flags.getArgFormat() != CallFlags::Standard) {
        TRACE_PRINTF("failing: not standard arg format\n");
        return ICInterpretOpResult::NextIC;
      }

      // For now, fail any arg-underflow case.
      if (argc < callee->nargs()) {
        TRACE_PRINTF("failing: too few args\n");
        return ICInterpretOpResult::NextIC;
      }

      uint32_t extra = 1 + flags.isConstructing() + isNative;
      uint32_t totalArgs = argc + extra;

      {
        PUSH_IC_FRAME();

        // Args above baseline frame.
        StackVal* origArgs =
            stack.fp + sizeof(BaselineStubFrameLayout) / sizeof(StackVal);

        // Push args.
        for (uint32_t i = 0; i < totalArgs; i++) {
          if (!stack.push(origArgs[i])) {
            return ICInterpretOpResult::Error;
          }
        }
        Value* args = reinterpret_cast<Value*>(stack.cur());

        if (!stack.push(StackVal(
                CalleeToToken(callee, /* isConstructing = */ false)))) {
          return ICInterpretOpResult::Error;
        }
        if (!stack.push(StackVal(MakeFrameDescriptorForJitCall(
                FrameType::BaselineStub, totalArgs)))) {
          return ICInterpretOpResult::Error;
        }
        if (!stack.push(StackVal(nullptr))) {  // fake return address.
          return ICInterpretOpResult::Error;
        }

        if (isNative) {
          JSNative native = ignoresRv
                                ? callee->jitInfo()->ignoresReturnValueMethod
                                : callee->native();
          if (!native(cx, argc, args)) {
            return ICInterpretOpResult::Error;
          }
          state.icResult = args[0].asRawBits();
        } else {
          if (!PortableBaselineInterpret(
                  cx, stack, /* envChain = */ nullptr,
                  reinterpret_cast<Value*>(&state.icResult))) {
            return ICInterpretOpResult::Error;
          }
        }
      }

      break;
    }

    case CacheOp::AssertPropertyLookup: {
      ObjOperandId objId = state.cacheIRReader.objOperandId();
      uint32_t idOffset = state.cacheIRReader.stubOffset();
      uint32_t slotOffset = state.cacheIRReader.stubOffset();
      // Debug-only assertion; we can ignore.
      (void)objId;
      (void)idOffset;
      (void)slotOffset;
      break;
    }

    case CacheOp::CallInt32ToString: {
      Int32OperandId inputId = state.cacheIRReader.int32OperandId();
      StringOperandId resultId = state.cacheIRReader.stringOperandId();
      int32_t input = int32_t(state.icVals[inputId.id()]);
      JSLinearString* str =
          Int32ToStringPure(frameMgr.cxForLocalUseOnly(), input);
      if (str) {
        state.icVals[resultId.id()] = reinterpret_cast<uintptr_t>(str);
      } else {
        return ICInterpretOpResult::NextIC;
      }
      break;
    }

    case CacheOp::CallStringConcatResult: {
      TRACE_PRINTF("CallStringConcatResult\n");
      StringOperandId lhsId = state.cacheIRReader.stringOperandId();
      StringOperandId rhsId = state.cacheIRReader.stringOperandId();
      // We don't push a frame and do a CanGC invocation here; we do a
      // pure (NoGC) invocation only, because it's cheaper.
      FakeRooted<JSString*> lhs(
          nullptr, reinterpret_cast<JSString*>(state.icVals[lhsId.id()]));
      FakeRooted<JSString*> rhs(
          nullptr, reinterpret_cast<JSString*>(state.icVals[rhsId.id()]));
      JSString* result =
          ConcatStrings<NoGC>(frameMgr.cxForLocalUseOnly(), lhs, rhs);
      if (result) {
        state.icResult = StringValue(result).asRawBits();
      } else {
        return ICInterpretOpResult::NextIC;
      }
      break;
    }

    default:
      printf("unknown CacheOp: %s\n", CacheIROpNames[int(op)]);
      return ICInterpretOpResult::NextIC;
  }

  return ICInterpretOpResult::Ok;
}

#define NEXT_IC() frame->interpreterICEntry()++;

#define INVOKE_IC(kind)                               \
  if (!IC##kind(frame, frameMgr, stack, state, pc)) { \
    goto error;                                       \
  }                                                   \
  NEXT_IC();

#define SAVE_INPUTS(arity)           \
  do {                               \
    switch (arity) {                 \
      case 0:                        \
        break;                       \
      case 1:                        \
        inputs[0] = state.icVals[0]; \
        break;                       \
      case 2:                        \
        inputs[0] = state.icVals[0]; \
        inputs[1] = state.icVals[1]; \
        break;                       \
      case 3:                        \
        inputs[0] = state.icVals[0]; \
        inputs[1] = state.icVals[1]; \
        inputs[2] = state.icVals[2]; \
        break;                       \
    }                                \
  } while (0)

#define RESTORE_INPUTS(arity)        \
  do {                               \
    switch (arity) {                 \
      case 0:                        \
        break;                       \
      case 1:                        \
        state.icVals[0] = inputs[0]; \
        break;                       \
      case 2:                        \
        state.icVals[0] = inputs[0]; \
        state.icVals[1] = inputs[1]; \
        break;                       \
      case 3:                        \
        state.icVals[0] = inputs[0]; \
        state.icVals[1] = inputs[1]; \
        state.icVals[2] = inputs[2]; \
        break;                       \
    }                                \
  } while (0)

#define DEFINE_IC(kind, arity, fallback_body)                                \
  static bool MOZ_ALWAYS_INLINE IC##kind(                                    \
      BaselineFrame* frame, VMFrameManager& frameMgr, Stack& stack,          \
      State& state, jsbytecode* pc) {                                        \
    ICStub* stub = frame->interpreterICEntry()->firstStub();                 \
    uint64_t inputs[3];                                                      \
    SAVE_INPUTS(arity);                                                      \
    while (true) {                                                           \
    next_stub:                                                               \
      if (stub->isFallback()) {                                              \
        ICFallbackStub* fallback = stub->toFallbackStub();                   \
        fallback_body;                                                       \
        state.icResult = state.res.asRawBits();                              \
        return true;                                                         \
      error:                                                                 \
        return false;                                                        \
      } else {                                                               \
        ICCacheIRStub* cstub = stub->toCacheIRStub();                        \
        cstub->incrementEnteredCount();                                      \
        new (&state.cacheIRReader) CacheIRReader(cstub->stubInfo()->code()); \
        while (true) {                                                       \
          switch (ICInterpretOp(frame, frameMgr, stack, state, cstub, pc)) { \
            case ICInterpretOpResult::NextIC:                                \
              stub = stub->maybeNext();                                      \
              RESTORE_INPUTS(arity);                                         \
              goto next_stub;                                                \
            case ICInterpretOpResult::Ok:                                    \
              continue;                                                      \
            case ICInterpretOpResult::Return:                                \
              return true;                                                   \
            case ICInterpretOpResult::Error:                                 \
              return false;                                                  \
          }                                                                  \
        }                                                                    \
      }                                                                      \
    }                                                                        \
  }

#define IC_LOAD_VAL(state_elem, index) \
  state.state_elem = Value::fromRawBits(state.icVals[(index)]);
#define IC_LOAD_OBJ(state_elem, index) \
  state.state_elem = reinterpret_cast<JSObject*>(state.icVals[(index)]);

#define PUSH_FALLBACK_IC_FRAME() \
  PUSH_EXIT_FRAME_OR_RET(false); \
  stack[0] = StackVal(fallback);

DEFINE_IC(Typeof, 1, {
  IC_LOAD_VAL(value0, 0);
  PUSH_FALLBACK_IC_FRAME();
  if (!DoTypeOfFallback(cx, frame, fallback, state.value0, &state.res)) {
    goto error;
  }
});

DEFINE_IC(GetName, 1, {
  IC_LOAD_OBJ(obj0, 0);
  PUSH_FALLBACK_IC_FRAME();
  if (!DoGetNameFallback(cx, frame, fallback, state.obj0, &state.res)) {
    goto error;
  }
});

DEFINE_IC(Call, 1, {
  uint32_t argc = uint32_t(state.icVals[0]);
  uint32_t totalArgs =
      argc + state.extraArgs;  // this, callee, (cosntructing?), func args
  Value* args = reinterpret_cast<Value*>(&stack[0]);
  TRACE_PRINTF("Call fallback: argc %d totalArgs %d args %p\n", argc, totalArgs,
               args);
  // Reverse values on the stack.
  for (uint32_t i = 0; i < totalArgs / 2; i++) {
    std::swap(args[i], args[totalArgs - 1 - i]);
  }
  {
    PUSH_FALLBACK_IC_FRAME();
    if (state.spreadCall) {
      if (!DoSpreadCallFallback(cx, frame, fallback, args, &state.res)) {
        goto error;
      }
    } else {
      if (!DoCallFallback(cx, frame, fallback, argc, args, &state.res)) {
        goto error;
      }
    }
  }
});

DEFINE_IC(UnaryArith, 1, {
  IC_LOAD_VAL(value0, 0);
  PUSH_FALLBACK_IC_FRAME();
  if (!DoUnaryArithFallback(cx, frame, fallback, state.value0, &state.res)) {
    goto error;
  }
});

DEFINE_IC(BinaryArith, 2, {
  IC_LOAD_VAL(value0, 0);
  IC_LOAD_VAL(value1, 1);
  PUSH_FALLBACK_IC_FRAME();
  if (!DoBinaryArithFallback(cx, frame, fallback, state.value0, state.value1,
                             &state.res)) {
    goto error;
  }
});

DEFINE_IC(ToBool, 1, {
  IC_LOAD_VAL(value0, 0);
  PUSH_FALLBACK_IC_FRAME();
  if (!DoToBoolFallback(cx, frame, fallback, state.value0, &state.res)) {
    goto error;
  }
});

DEFINE_IC(Compare, 2, {
  IC_LOAD_VAL(value0, 0);
  IC_LOAD_VAL(value1, 1);
  PUSH_FALLBACK_IC_FRAME();
  if (!DoCompareFallback(cx, frame, fallback, state.value0, state.value1,
                         &state.res)) {
    goto error;
  }
});

DEFINE_IC(InstanceOf, 2, {
  IC_LOAD_VAL(value0, 0);
  IC_LOAD_VAL(value1, 1);
  PUSH_FALLBACK_IC_FRAME();
  if (!DoInstanceOfFallback(cx, frame, fallback, state.value0, state.value1,
                            &state.res)) {
    goto error;
  }
});

DEFINE_IC(In, 2, {
  IC_LOAD_VAL(value0, 0);
  IC_LOAD_VAL(value1, 1);
  PUSH_FALLBACK_IC_FRAME();
  if (!DoInFallback(cx, frame, fallback, state.value0, state.value1,
                    &state.res)) {
    goto error;
  }
});

DEFINE_IC(BindName, 1, {
  IC_LOAD_OBJ(obj0, 0);
  PUSH_FALLBACK_IC_FRAME();
  if (!DoBindNameFallback(cx, frame, fallback, state.obj0, &state.res)) {
    goto error;
  }
});

DEFINE_IC(SetProp, 2, {
  IC_LOAD_VAL(value0, 0);
  IC_LOAD_VAL(value1, 1);
  PUSH_FALLBACK_IC_FRAME();
  if (!DoSetPropFallback(cx, frame, fallback, nullptr, state.value0,
                         state.value1)) {
    goto error;
  }
});

DEFINE_IC(NewObject, 0, {
  PUSH_FALLBACK_IC_FRAME();
  if (!DoNewObjectFallback(cx, frame, fallback, &state.res)) {
    goto error;
  }
});

DEFINE_IC(GetProp, 1, {
  IC_LOAD_VAL(value0, 0);
  PUSH_FALLBACK_IC_FRAME();
  if (!DoGetPropFallback(cx, frame, fallback, &state.value0, &state.res)) {
    goto error;
  }
});

DEFINE_IC(GetPropSuper, 2, {
  IC_LOAD_VAL(value0, 0);
  IC_LOAD_VAL(value1, 1);
  PUSH_FALLBACK_IC_FRAME();
  if (!DoGetPropSuperFallback(cx, frame, fallback, state.value0, &state.value1,
                              &state.res)) {
    goto error;
  }
});

DEFINE_IC(GetElem, 2, {
  IC_LOAD_VAL(value0, 0);
  IC_LOAD_VAL(value1, 1);
  PUSH_FALLBACK_IC_FRAME();
  if (!DoGetElemFallback(cx, frame, fallback, state.value0, state.value1,
                         &state.res)) {
    goto error;
  }
});

DEFINE_IC(GetElemSuper, 3, {
  IC_LOAD_VAL(value0, 0);
  IC_LOAD_VAL(value1, 1);
  IC_LOAD_VAL(value2, 2);
  PUSH_FALLBACK_IC_FRAME();
  if (!DoGetElemSuperFallback(cx, frame, fallback, state.value0, state.value1,
                              state.value2, &state.res)) {
    goto error;
  }
});

DEFINE_IC(NewArray, 0, {
  PUSH_FALLBACK_IC_FRAME();
  if (!DoNewArrayFallback(cx, frame, fallback, &state.res)) {
    goto error;
  }
});

DEFINE_IC(GetIntrinsic, 0, {
  PUSH_FALLBACK_IC_FRAME();
  if (!DoGetIntrinsicFallback(cx, frame, fallback, &state.res)) {
    goto error;
  }
});

DEFINE_IC(SetElem, 3, {
  IC_LOAD_VAL(value0, 0);
  IC_LOAD_VAL(value1, 1);
  IC_LOAD_VAL(value2, 2);
  PUSH_FALLBACK_IC_FRAME();
  if (!DoSetElemFallback(cx, frame, fallback, nullptr, state.value0,
                         state.value1, state.value2)) {
    goto error;
  }
});

DEFINE_IC(HasOwn, 2, {
  IC_LOAD_VAL(value0, 0);
  IC_LOAD_VAL(value1, 1);
  PUSH_FALLBACK_IC_FRAME();
  if (!DoHasOwnFallback(cx, frame, fallback, state.value0, state.value1,
                        &state.res)) {
    goto error;
  }
});

DEFINE_IC(CheckPrivateField, 2, {
  IC_LOAD_VAL(value0, 0);
  IC_LOAD_VAL(value1, 1);
  PUSH_FALLBACK_IC_FRAME();
  if (!DoCheckPrivateFieldFallback(cx, frame, fallback, state.value0,
                                   state.value1, &state.res)) {
    goto error;
  }
});

DEFINE_IC(GetIterator, 1, {
  IC_LOAD_VAL(value0, 0);
  PUSH_FALLBACK_IC_FRAME();
  if (!DoGetIteratorFallback(cx, frame, fallback, state.value0, &state.res)) {
    goto error;
  }
});

DEFINE_IC(ToPropertyKey, 1, {
  IC_LOAD_VAL(value0, 0);
  PUSH_FALLBACK_IC_FRAME();
  if (!DoToPropertyKeyFallback(cx, frame, fallback, state.value0, &state.res)) {
    goto error;
  }
});

DEFINE_IC(OptimizeSpreadCall, 1, {
  IC_LOAD_VAL(value0, 0);
  PUSH_FALLBACK_IC_FRAME();
  if (!DoOptimizeSpreadCallFallback(cx, frame, fallback, state.value0,
                                    &state.res)) {
    goto error;
  }
});

DEFINE_IC(Rest, 0, {
  PUSH_FALLBACK_IC_FRAME();
  if (!DoRestFallback(cx, frame, fallback, &state.res)) {
    goto error;
  }
});

DEFINE_IC(CloseIter, 1, {
  IC_LOAD_OBJ(obj0, 0);
  PUSH_FALLBACK_IC_FRAME();
  if (!DoCloseIterFallback(cx, frame, fallback, state.obj0)) {
    goto error;
  }
});

#define PUSH_EXIT_FRAME() PUSH_EXIT_FRAME_OR_RET(false)

static bool PortableBaselineInterpret(JSContext* cx_, Stack& stack,
                                      JSObject* envChain, Value* ret) {
  State state(cx_);

  TRY(stack.pushFrame(cx_, envChain));

  BaselineFrame* frame = stack.frameFromFP();
  RootedScript script(cx_, frame->script());
  jsbytecode* pc = frame->interpreterPC();

  uint32_t nslots = script->nslots();
  for (uint32_t i = 0; i < nslots; i++) {
    TRY(stack.push(StackVal(UndefinedValue())));
  }
  ret->setUndefined();

  VMFrameManager frameMgr(cx_, frame);

  if (CalleeTokenIsFunction(frame->calleeToken())) {
    JSFunction* func = CalleeTokenToFunction(frame->calleeToken());
    frame->setEnvironmentChain(func->environment());
    if (func->needsFunctionEnvironmentObjects()) {
      PUSH_EXIT_FRAME();
      TRY(js::InitFunctionEnvironmentObjects(cx, frame));
    }
  }

  while (true) {
  dispatch:

#define ADVANCE(delta) pc += (delta);
#define ADVANCE_AND_DISPATCH(delta) \
  ADVANCE(delta);                   \
  goto dispatch;

#define END_OP(op) ADVANCE_AND_DISPATCH(JSOpLength_##op);

#define IC_SET_ARG_FROM_STACK(index, stack_index) \
  state.icVals[(index)] = stack[(stack_index)].asUInt64();
#define IC_POP_ARG(index) state.icVals[(index)] = stack.pop().asUInt64();
#define IC_SET_VAL_ARG(index, expr) state.icVals[(index)] = (expr).asRawBits();
#define IC_SET_OBJ_ARG(index, expr) \
  state.icVals[(index)] = reinterpret_cast<uint64_t>(expr);
#define IC_PUSH_RESULT() PUSH(StackVal(state.icResult));

    JSOp op = JSOp(*pc);

#ifdef TRACE_INTERP
    printf("stack[0] = %" PRIx64 " stack[1] = %" PRIx64 " stack[2] = %" PRIx64
           "\n",
           stack[0].asUInt64(), stack[1].asUInt64(), stack[2].asUInt64());
    printf("script = %p pc = %p: %s (ic %d) pending = %d\n", script.get(), pc,
           CodeName(op),
           (int)(frame->interpreterICEntry() -
                 script->jitScript()->icScript()->icEntries()),
           frameMgr.cxForLocalUseOnly()->isExceptionPending());
    printf("TOS tag: %d\n", int(stack[0].asValue().asRawBits() >> 47));
    fflush(stdout);
#endif

    switch (op) {
      case JSOp::Nop: {
        END_OP(Nop);
      }
      case JSOp::Undefined: {
        PUSH(StackVal(UndefinedValue()));
        END_OP(Undefined);
      }
      case JSOp::Null: {
        PUSH(StackVal(NullValue()));
        END_OP(Null);
      }
      case JSOp::False: {
        PUSH(StackVal(BooleanValue(false)));
        END_OP(False);
      }
      case JSOp::True: {
        PUSH(StackVal(BooleanValue(true)));
        END_OP(True);
      }
      case JSOp::Int32: {
        PUSH(StackVal(Int32Value(GET_INT32(pc))));
        END_OP(Int32);
      }
      case JSOp::Zero: {
        PUSH(StackVal(Int32Value(0)));
        END_OP(Zero);
      }
      case JSOp::One: {
        PUSH(StackVal(Int32Value(1)));
        END_OP(One);
      }
      case JSOp::Int8: {
        PUSH(StackVal(Int32Value(GET_INT8(pc))));
        END_OP(Int8);
      }
      case JSOp::Uint16: {
        PUSH(StackVal(Int32Value(GET_UINT16(pc))));
        END_OP(Uint16);
      }
      case JSOp::Uint24: {
        PUSH(StackVal(Int32Value(GET_UINT24(pc))));
        END_OP(Uint24);
      }
      case JSOp::Double: {
        PUSH(StackVal(GET_INLINE_VALUE(pc)));
        END_OP(Double);
      }
      case JSOp::BigInt: {
        PUSH(StackVal(JS::BigIntValue(script->getBigInt(pc))));
        END_OP(BigInt);
      }
      case JSOp::String: {
        PUSH(StackVal(StringValue(script->getString(pc))));
        END_OP(String);
      }
      case JSOp::Symbol: {
        PUSH(StackVal(
            SymbolValue(frameMgr.cxForLocalUseOnly()->wellKnownSymbols().get(
                GET_UINT8(pc)))));
        END_OP(Symbol);
      }
      case JSOp::Void: {
        stack[0] = StackVal(JS::UndefinedValue());
        END_OP(Void);
      }

      case JSOp::Typeof:
      case JSOp::TypeofExpr: {
        static_assert(JSOpLength_Typeof == JSOpLength_TypeofExpr);
        IC_POP_ARG(0);
        INVOKE_IC(Typeof);
        IC_PUSH_RESULT();
        END_OP(Typeof);
      }

      case JSOp::Pos:
      case JSOp::Neg:
      case JSOp::BitNot:
      case JSOp::Inc:
      case JSOp::Dec:
      case JSOp::ToNumeric: {
        static_assert(JSOpLength_Pos == JSOpLength_Neg);
        static_assert(JSOpLength_Pos == JSOpLength_BitNot);
        static_assert(JSOpLength_Pos == JSOpLength_Inc);
        static_assert(JSOpLength_Pos == JSOpLength_Dec);
        static_assert(JSOpLength_Pos == JSOpLength_ToNumeric);
        IC_POP_ARG(0);
        INVOKE_IC(UnaryArith);
        IC_PUSH_RESULT();
        END_OP(Pos);
      }
      case JSOp::Not: {
        IC_POP_ARG(0);
        INVOKE_IC(ToBool);
        PUSH(StackVal(
            BooleanValue(!Value::fromRawBits(state.icResult).toBoolean())));
        END_OP(Not);
      }
      case JSOp::And: {
        IC_SET_ARG_FROM_STACK(0, 0);
        INVOKE_IC(ToBool);
        uint32_t jumpOffset = GET_JUMP_OFFSET(pc);
        bool result = Value::fromRawBits(state.icResult).toBoolean();
        if (!result) {
          ADVANCE(jumpOffset);
        } else {
          ADVANCE(JSOpLength_And);
        }
        break;
      }
      case JSOp::Or: {
        IC_SET_ARG_FROM_STACK(0, 0);
        INVOKE_IC(ToBool);
        uint32_t jumpOffset = GET_JUMP_OFFSET(pc);
        bool result = Value::fromRawBits(state.icResult).toBoolean();
        if (result) {
          ADVANCE(jumpOffset);
        } else {
          ADVANCE(JSOpLength_Or);
        }
        break;
      }
      case JSOp::JumpIfTrue: {
        IC_POP_ARG(0);
        INVOKE_IC(ToBool);
        uint32_t jumpOffset = GET_JUMP_OFFSET(pc);
        bool result = Value::fromRawBits(state.icResult).toBoolean();
        if (result) {
          ADVANCE(jumpOffset);
        } else {
          ADVANCE(JSOpLength_JumpIfTrue);
        }
        break;
      }
      case JSOp::JumpIfFalse: {
        IC_POP_ARG(0);
        INVOKE_IC(ToBool);
        uint32_t jumpOffset = GET_JUMP_OFFSET(pc);
        bool result = Value::fromRawBits(state.icResult).toBoolean();
        if (!result) {
          ADVANCE(jumpOffset);
        } else {
          ADVANCE(JSOpLength_JumpIfFalse);
        }
        break;
      }

      case JSOp::BitOr:
      case JSOp::BitXor:
      case JSOp::BitAnd:
      case JSOp::Lsh:
      case JSOp::Rsh:
      case JSOp::Ursh:
      case JSOp::Add:
      case JSOp::Sub:
      case JSOp::Mul:
      case JSOp::Div:
      case JSOp::Mod:
      case JSOp::Pow: {
        static_assert(JSOpLength_BitOr == JSOpLength_BitXor);
        static_assert(JSOpLength_BitOr == JSOpLength_BitAnd);
        static_assert(JSOpLength_BitOr == JSOpLength_Lsh);
        static_assert(JSOpLength_BitOr == JSOpLength_Rsh);
        static_assert(JSOpLength_BitOr == JSOpLength_Ursh);
        static_assert(JSOpLength_BitOr == JSOpLength_Add);
        static_assert(JSOpLength_BitOr == JSOpLength_Sub);
        static_assert(JSOpLength_BitOr == JSOpLength_Mul);
        static_assert(JSOpLength_BitOr == JSOpLength_Div);
        static_assert(JSOpLength_BitOr == JSOpLength_Mod);
        static_assert(JSOpLength_BitOr == JSOpLength_Pow);
        IC_POP_ARG(1);
        IC_POP_ARG(0);
        INVOKE_IC(BinaryArith);
        IC_PUSH_RESULT();
        END_OP(Div);
      }

      case JSOp::Eq:
      case JSOp::Ne:
      case JSOp::StrictEq:
      case JSOp::StrictNe:
      case JSOp::Lt:
      case JSOp::Gt:
      case JSOp::Le:
      case JSOp::Ge: {
        static_assert(JSOpLength_Eq == JSOpLength_Ne);
        static_assert(JSOpLength_Eq == JSOpLength_StrictEq);
        static_assert(JSOpLength_Eq == JSOpLength_StrictNe);
        static_assert(JSOpLength_Eq == JSOpLength_Lt);
        static_assert(JSOpLength_Eq == JSOpLength_Gt);
        static_assert(JSOpLength_Eq == JSOpLength_Le);
        static_assert(JSOpLength_Eq == JSOpLength_Ge);
        IC_POP_ARG(1);
        IC_POP_ARG(0);
        INVOKE_IC(Compare);
        IC_PUSH_RESULT();
        END_OP(Eq);
      }

      case JSOp::Instanceof: {
        IC_POP_ARG(1);
        IC_POP_ARG(0);
        INVOKE_IC(InstanceOf);
        IC_PUSH_RESULT();
        END_OP(Instanceof);
      }

      case JSOp::In: {
        IC_POP_ARG(1);
        IC_POP_ARG(0);
        INVOKE_IC(In);
        IC_PUSH_RESULT();
        END_OP(In);
      }

      case JSOp::ToPropertyKey: {
        IC_POP_ARG(0);
        INVOKE_IC(ToPropertyKey);
        IC_PUSH_RESULT();
        END_OP(ToPropertyKey);
      }

      case JSOp::ToString: {
        state.value0 = stack.pop().asValue();
        JSString* result;
        {
          PUSH_EXIT_FRAME();
          result = ToString<CanGC>(cx, state.value0);
          if (!result) {
            goto error;
          }
        }
        PUSH(StackVal(StringValue(result)));
        END_OP(ToString);
      }

      case JSOp::IsNullOrUndefined: {
        bool result =
            stack[0].asValue().isNull() || stack[0].asValue().isUndefined();
        stack[0] = StackVal(BooleanValue(result));
        END_OP(IsNullOrUndefined);
      }

      case JSOp::GlobalThis: {
        PUSH(StackVal(ObjectValue(*frameMgr.cxForLocalUseOnly()
                                       ->global()
                                       ->lexicalEnvironment()
                                       .thisObject())));
        END_OP(GlobalThis);
      }

      case JSOp::NonSyntacticGlobalThis: {
        {
          PUSH_EXIT_FRAME();
          state.obj0 = frame->environmentChain();
          js::GetNonSyntacticGlobalThis(cx, state.obj0, &state.value0);
        }
        PUSH(StackVal(state.value0));
        END_OP(NonSyntacticGlobalThis);
      }

      case JSOp::NewTarget: {
        PUSH(StackVal(frame->newTarget()));
        END_OP(NewTarget);
      }

      case JSOp::DynamicImport: {
        state.value0 = stack.pop().asValue();  // options
        state.value1 = stack.pop().asValue();  // specifier
        JSObject* promise;
        {
          PUSH_EXIT_FRAME();
          promise =
              StartDynamicModuleImport(cx, script, state.value1, state.value0);
          if (!promise) {
            goto error;
          }
        }
        PUSH(StackVal(ObjectValue(*promise)));
        END_OP(DynamicImport);
      }

      case JSOp::ImportMeta: {
        JSObject* metaObject;
        {
          PUSH_EXIT_FRAME();
          metaObject = ImportMetaOperation(cx, script);
          if (!metaObject) {
            goto error;
          }
        }
        PUSH(StackVal(ObjectValue(*metaObject)));
        END_OP(ImportMeta);
      }

      case JSOp::NewInit: {
        INVOKE_IC(NewObject);
        IC_PUSH_RESULT();
        END_OP(NewInit);
      }
      case JSOp::NewObject: {
        INVOKE_IC(NewObject);
        IC_PUSH_RESULT();
        END_OP(NewObject);
      }
      case JSOp::Object: {
        PUSH(StackVal(ObjectValue(*script->getObject(pc))));
        END_OP(Object);
      }
      case JSOp::ObjWithProto: {
        state.value0 = stack[0].asValue();
        JSObject* obj;
        {
          PUSH_EXIT_FRAME();
          obj = ObjectWithProtoOperation(cx, state.value0);
        }
        stack[0] = StackVal(ObjectValue(*obj));
        END_OP(ObjWithProto);
      }

      case JSOp::InitElem:
      case JSOp::InitHiddenElem:
      case JSOp::InitLockedElem:
      case JSOp::InitElemInc:
      case JSOp::SetElem:
      case JSOp::StrictSetElem: {
        static_assert(JSOpLength_InitElem == JSOpLength_InitHiddenElem);
        static_assert(JSOpLength_InitElem == JSOpLength_InitLockedElem);
        static_assert(JSOpLength_InitElem == JSOpLength_InitElemInc);
        static_assert(JSOpLength_InitElem == JSOpLength_SetElem);
        static_assert(JSOpLength_InitElem == JSOpLength_StrictSetElem);
        IC_POP_ARG(2);
        IC_POP_ARG(1);
        IC_SET_ARG_FROM_STACK(0, 0);
        INVOKE_IC(SetElem);
        if (op == JSOp::InitElemInc) {
          PUSH(StackVal(
              Int32Value(Value::fromRawBits(state.icVals[1]).toInt32() + 1)));
        }
        END_OP(InitElem);
      }

      case JSOp::InitPropGetter:
      case JSOp::InitHiddenPropGetter:
      case JSOp::InitPropSetter:
      case JSOp::InitHiddenPropSetter: {
        static_assert(JSOpLength_InitPropGetter ==
                      JSOpLength_InitHiddenPropGetter);
        static_assert(JSOpLength_InitPropGetter == JSOpLength_InitPropSetter);
        static_assert(JSOpLength_InitPropGetter ==
                      JSOpLength_InitHiddenPropSetter);
        state.obj1 = &stack.pop().asValue().toObject();  // val
        state.obj0 = &stack[0].asValue().toObject();     // obj; leave on stack
        state.name0 = script->getName(pc);
        {
          PUSH_EXIT_FRAME();
          if (!InitPropGetterSetterOperation(cx, pc, state.obj0, state.name0,
                                             state.obj1)) {
            goto error;
          }
        }
        END_OP(InitPropGetter);
      }

      case JSOp::InitElemGetter:
      case JSOp::InitHiddenElemGetter:
      case JSOp::InitElemSetter:
      case JSOp::InitHiddenElemSetter: {
        static_assert(JSOpLength_InitElemGetter ==
                      JSOpLength_InitHiddenElemGetter);
        static_assert(JSOpLength_InitElemGetter == JSOpLength_InitElemSetter);
        static_assert(JSOpLength_InitElemGetter ==
                      JSOpLength_InitHiddenElemSetter);
        state.obj1 = &stack.pop().asValue().toObject();  // val
        state.value0 = stack.pop().asValue();            // idval
        state.obj0 = &stack[0].asValue().toObject();     // obj; leave on stack
        {
          PUSH_EXIT_FRAME();
          if (!InitElemGetterSetterOperation(cx, pc, state.obj0, state.value0,
                                             state.obj1)) {
            goto error;
          }
        }
        END_OP(InitElemGetter);
      }

      case JSOp::GetProp:
      case JSOp::GetBoundName: {
        static_assert(JSOpLength_GetProp == JSOpLength_GetBoundName);
        IC_POP_ARG(0);
        INVOKE_IC(GetProp);
        IC_PUSH_RESULT();
        END_OP(GetProp);
      }
      case JSOp::GetPropSuper: {
        IC_POP_ARG(1);
        IC_POP_ARG(0);
        INVOKE_IC(GetPropSuper);
        IC_PUSH_RESULT();
        END_OP(GetPropSuper);
      }

      case JSOp::GetElem: {
        IC_POP_ARG(1);
        IC_POP_ARG(0);
        INVOKE_IC(GetElem);
        IC_PUSH_RESULT();
        END_OP(GetElem);
      }

      case JSOp::GetElemSuper: {
        IC_POP_ARG(2);
        IC_POP_ARG(1);
        IC_POP_ARG(0);
        INVOKE_IC(GetElemSuper);
        IC_PUSH_RESULT();
        END_OP(GetElemSuper);
      }

      case JSOp::DelProp: {
        state.value0 = stack.pop().asValue();
        state.name0 = script->getName(pc);
        bool res = false;
        {
          PUSH_EXIT_FRAME();
          if (!DelPropOperation<true>(cx, state.value0, state.name0, &res)) {
            goto error;
          }
        }
        PUSH(StackVal(BooleanValue(res)));
        END_OP(DelProp);
      }
      case JSOp::StrictDelProp: {
        state.value0 = stack.pop().asValue();
        state.name0 = script->getName(pc);
        bool res = false;
        {
          PUSH_EXIT_FRAME();
          if (!DelPropOperation<true>(cx, state.value0, state.name0, &res)) {
            goto error;
          }
        }
        PUSH(StackVal(BooleanValue(res)));
        END_OP(StrictDelProp);
      }
      case JSOp::DelElem: {
        state.value1 = stack.pop().asValue();
        state.value0 = stack.pop().asValue();
        bool res = false;
        {
          PUSH_EXIT_FRAME();
          if (!DelElemOperation<true>(cx, state.value0, state.value1, &res)) {
            goto error;
          }
        }
        PUSH(StackVal(BooleanValue(res)));
        END_OP(DelElem);
      }
      case JSOp::StrictDelElem: {
        state.value1 = stack.pop().asValue();
        state.value0 = stack.pop().asValue();
        bool res = false;
        {
          PUSH_EXIT_FRAME();
          if (!DelElemOperation<true>(cx, state.value0, state.value1, &res)) {
            goto error;
          }
        }
        PUSH(StackVal(BooleanValue(res)));
        END_OP(StrictDelElem);
      }

      case JSOp::HasOwn: {
        IC_POP_ARG(1);
        IC_POP_ARG(0);
        INVOKE_IC(HasOwn);
        IC_PUSH_RESULT();
        END_OP(HasOwn);
      }

      case JSOp::CheckPrivateField: {
        IC_SET_ARG_FROM_STACK(1, 1);
        IC_SET_ARG_FROM_STACK(0, 0);
        INVOKE_IC(CheckPrivateField);
        IC_PUSH_RESULT();
        END_OP(CheckPrivateField);
      }

      case JSOp::NewPrivateName: {
        state.atom0 = script->getAtom(pc);
        JS::Symbol* symbol;
        {
          PUSH_EXIT_FRAME();
          symbol = NewPrivateName(cx, state.atom0);
          if (!symbol) {
            goto error;
          }
        }
        PUSH(StackVal(SymbolValue(symbol)));
        END_OP(NewPrivateName);
      }

      case JSOp::SuperBase: {
        JSFunction& superEnvFunc =
            stack.pop().asValue().toObject().as<JSFunction>();
        MOZ_ASSERT(superEnvFunc.allowSuperProperty());
        MOZ_ASSERT(superEnvFunc.baseScript()->needsHomeObject());
        const Value& homeObjVal = superEnvFunc.getExtendedSlot(
            FunctionExtended::METHOD_HOMEOBJECT_SLOT);

        JSObject* homeObj = &homeObjVal.toObject();
        JSObject* superBase = HomeObjectSuperBase(homeObj);

        PUSH(StackVal(ObjectOrNullValue(superBase)));
        END_OP(SuperBase);
      }

      case JSOp::SetPropSuper:
      case JSOp::StrictSetPropSuper: {
        // stack signature: receiver, lval, rval => rval
        static_assert(JSOpLength_SetPropSuper == JSOpLength_StrictSetPropSuper);
        bool strict = op == JSOp::StrictSetPropSuper;
        state.value2 = stack.pop().asValue();  // rval
        state.value1 = stack.pop().asValue();  // lval
        state.value0 = stack.pop().asValue();  // receiver
        state.name0 = script->getName(pc);
        {
          PUSH_EXIT_FRAME();
          // SetPropertySuper(cx, lval, receiver, name, rval, strict)
          // (N.B.: lval and receiver are transposed!)
          if (!SetPropertySuper(cx, state.value1, state.value0, state.name0,
                                state.value2, strict)) {
            goto error;
          }
        }
        PUSH(StackVal(state.value2));
        END_OP(SetPropSuper);
      }

      case JSOp::SetElemSuper:
      case JSOp::StrictSetElemSuper: {
        // stack signature: receiver, key, lval, rval => rval
        static_assert(JSOpLength_SetElemSuper == JSOpLength_StrictSetElemSuper);
        bool strict = op == JSOp::StrictSetElemSuper;
        state.value3 = stack.pop().asValue();  // rval
        state.value2 = stack.pop().asValue();  // lval
        state.value1 = stack.pop().asValue();  // index
        state.value0 = stack.pop().asValue();  // receiver
        {
          PUSH_EXIT_FRAME();
          // SetElementSuper(cx, lval, receiver, index, rval, strict)
          // (N.B.: lval, receiver and index are rotated!)
          if (!SetElementSuper(cx, state.value2, state.value0, state.value1,
                               state.value3, strict)) {
            goto error;
          }
        }
        PUSH(StackVal(state.value2));  // value
        END_OP(SetElemSuper);
      }

      case JSOp::Iter: {
        IC_POP_ARG(0);
        INVOKE_IC(GetIterator);
        IC_PUSH_RESULT();
        END_OP(Iter);
      }

      case JSOp::MoreIter: {
        // iter => iter, name
        Value v = IteratorMore(&stack[0].asValue().toObject());
        PUSH(StackVal(v));
        END_OP(MoreIter);
      }

      case JSOp::IsNoIter: {
        // iter => iter, bool
        bool result = stack[0].asValue().isMagic(JS_NO_ITER_VALUE);
        PUSH(StackVal(BooleanValue(result)));
        END_OP(IsNoIter);
      }

      case JSOp::EndIter: {
        // iter, interval =>
        stack.pop();
        CloseIterator(&stack.pop().asValue().toObject());
        END_OP(EndIter);
      }

      case JSOp::CloseIter: {
        IC_SET_OBJ_ARG(0, &stack.pop().asValue().toObject());
        INVOKE_IC(CloseIter);
        END_OP(CloseIter);
      }

      case JSOp::CheckIsObj: {
        if (!stack[0].asValue().isObject()) {
          PUSH_EXIT_FRAME();
          MOZ_ALWAYS_FALSE(
              js::ThrowCheckIsObject(cx, js::CheckIsObjectKind(GET_UINT8(pc))));
          goto error;
        }
        END_OP(CheckIsObj);
      }

      case JSOp::CheckObjCoercible: {
        state.value0 = stack[0].asValue();
        if (state.value0.isNullOrUndefined()) {
          PUSH_EXIT_FRAME();
          MOZ_ALWAYS_FALSE(ThrowObjectCoercible(cx, state.value0));
          goto error;
        }
        END_OP(CheckObjCoercible);
      }

      case JSOp::ToAsyncIter: {
        // iter, next => asynciter
        state.value0 = stack.pop().asValue();            // next
        state.obj0 = &stack.pop().asValue().toObject();  // iter

        JSObject* ret;
        {
          PUSH_EXIT_FRAME();
          ret = CreateAsyncFromSyncIterator(cx, state.obj0, state.value0);
          if (!ret) {
            goto error;
          }
        }
        PUSH(StackVal(ObjectValue(*ret)));
        END_OP(ToAsyncIter);
      }

      case JSOp::MutateProto: {
        // obj, protoVal => obj
        state.value0 = stack.pop().asValue();
        state.obj0 = &stack[0].asValue().toObject();
        {
          PUSH_EXIT_FRAME();
          if (!MutatePrototype(cx, state.obj0.as<PlainObject>(),
                               state.value0)) {
            goto error;
          }
        }
        END_OP(MutateProto);
      }

      case JSOp::NewArray: {
        INVOKE_IC(NewArray);
        IC_PUSH_RESULT();
        END_OP(NewArray);
      }

      case JSOp::InitElemArray: {
        // array, val => array
        state.value0 = stack.pop().asValue();
        state.obj0 = &stack[0].asValue().toObject();
        {
          PUSH_EXIT_FRAME();
          InitElemArrayOperation(cx, pc, state.obj0.as<ArrayObject>(),
                                 state.value0);
        }
        END_OP(InitElemArray);
      }

      case JSOp::Hole: {
        PUSH(StackVal(MagicValue(JS_ELEMENTS_HOLE)));
        END_OP(Hole);
      }

      case JSOp::RegExp: {
        JSObject* obj;
        {
          PUSH_EXIT_FRAME();
          state.obj0 = script->getRegExp(pc);
          obj = CloneRegExpObject(cx, state.obj0.as<RegExpObject>());
          if (!obj) {
            goto error;
          }
        }
        PUSH(StackVal(ObjectValue(*obj)));
        END_OP(RegExp);
      }

      case JSOp::Lambda: {
        state.fun0 = script->getFunction(pc);
        state.obj0 = frame->environmentChain();
        JSObject* res;
        {
          PUSH_EXIT_FRAME();
          res = js::Lambda(cx, state.fun0, state.obj0);
          if (!res) {
            goto error;
          }
        }
        PUSH(StackVal(ObjectValue(*res)));
        END_OP(Lambda);
      }

      case JSOp::SetFunName: {
        // fun, name => fun
        state.value0 = stack.pop().asValue();  // name
        state.fun0 = &stack[0].asValue().toObject().as<JSFunction>();
        FunctionPrefixKind prefixKind = FunctionPrefixKind(GET_UINT8(pc));
        {
          PUSH_EXIT_FRAME();
          if (!SetFunctionName(cx, state.fun0, state.value0, prefixKind)) {
            goto error;
          }
        }
        END_OP(SetFunName);
      }

      case JSOp::InitHomeObject: {
        // fun, homeObject => fun
        state.obj0 = &stack.pop().asValue().toObject();  // homeObject
        state.fun0 = &stack[0].asValue().toObject().as<JSFunction>();
        MOZ_ASSERT(state.fun0->allowSuperProperty());
        MOZ_ASSERT(state.obj0->is<PlainObject>() ||
                   state.obj0->is<JSFunction>());
        state.fun0->setExtendedSlot(FunctionExtended::METHOD_HOMEOBJECT_SLOT,
                                    ObjectValue(*state.obj0));
        END_OP(InitHomeObject);
      }

      case JSOp::CheckClassHeritage: {
        state.value0 = stack[0].asValue();
        {
          PUSH_EXIT_FRAME();
          if (!CheckClassHeritageOperation(cx, state.value0)) {
            goto error;
          }
        }
        END_OP(CheckClassHeritage);
      }

      case JSOp::FunWithProto: {
        // proto => obj
        state.obj0 = &stack.pop().asValue().toObject();  // proto
        state.obj1 = frame->environmentChain();
        state.fun0 = script->getFunction(pc);
        JSObject* obj;
        {
          PUSH_EXIT_FRAME();
          obj = FunWithProtoOperation(cx, state.fun0, state.obj1, state.obj0);
          if (!obj) {
            goto error;
          }
        }
        PUSH(StackVal(ObjectValue(*obj)));
        END_OP(FunWithProto);
      }

      case JSOp::BuiltinObject: {
        auto kind = BuiltinObjectKind(GET_UINT8(pc));
        JSObject* builtin;
        {
          PUSH_EXIT_FRAME();
          builtin = BuiltinObjectOperation(cx, kind);
          if (!builtin) {
            goto error;
          }
        }
        PUSH(StackVal(ObjectValue(*builtin)));
        END_OP(BuiltinObject);
      }

      case JSOp::Call:
      case JSOp::CallIgnoresRv:
      case JSOp::CallContent:
      case JSOp::CallIter:
      case JSOp::CallContentIter:
      case JSOp::Eval:
      case JSOp::StrictEval: {
        static_assert(JSOpLength_Call == JSOpLength_CallIgnoresRv);
        static_assert(JSOpLength_Call == JSOpLength_CallContent);
        static_assert(JSOpLength_Call == JSOpLength_CallIter);
        static_assert(JSOpLength_Call == JSOpLength_CallContentIter);
        static_assert(JSOpLength_Call == JSOpLength_Eval);
        static_assert(JSOpLength_Call == JSOpLength_StrictEval);
        uint32_t argc = GET_ARGC(pc);
        state.icVals[0] = argc;
        state.extraArgs = 2;
        state.spreadCall = false;
        INVOKE_IC(Call);
        stack.popn(argc + 2);
        PUSH(StackVal(Value::fromRawBits(state.icResult)));
        END_OP(Call);
      }

      case JSOp::SuperCall:
      case JSOp::New:
      case JSOp::NewContent: {
        static_assert(JSOpLength_SuperCall == JSOpLength_New);
        static_assert(JSOpLength_SuperCall == JSOpLength_NewContent);
        uint32_t argc = GET_ARGC(pc);
        state.icVals[0] = argc;
        state.extraArgs = 3;
        state.spreadCall = false;
        INVOKE_IC(Call);
        stack.popn(argc + 3);
        PUSH(StackVal(Value::fromRawBits(state.icResult)));
        END_OP(SuperCall);
      }

      case JSOp::SpreadCall:
      case JSOp::SpreadEval:
      case JSOp::StrictSpreadEval: {
        static_assert(JSOpLength_SpreadCall == JSOpLength_SpreadEval);
        static_assert(JSOpLength_SpreadCall == JSOpLength_StrictSpreadEval);
        state.icVals[0] = 1;
        state.extraArgs = 2;
        state.spreadCall = true;
        INVOKE_IC(Call);
        stack.popn(3);
        PUSH(StackVal(Value::fromRawBits(state.icResult)));
        END_OP(SpreadCall);
      }

      case JSOp::SpreadSuperCall:
      case JSOp::SpreadNew: {
        static_assert(JSOpLength_SpreadSuperCall == JSOpLength_SpreadNew);
        state.icVals[0] = 1;
        state.extraArgs = 3;
        state.spreadCall = true;
        INVOKE_IC(Call);
        stack.popn(4);
        PUSH(StackVal(Value::fromRawBits(state.icResult)));
        END_OP(SpreadSuperCall);
      }

      case JSOp::OptimizeSpreadCall: {
        IC_POP_ARG(0);
        INVOKE_IC(OptimizeSpreadCall);
        IC_PUSH_RESULT();
        END_OP(OptimizeSpreadCall);
      }

      case JSOp::ImplicitThis: {
        state.obj0 = frame->environmentChain();
        state.name0 = script->getName(pc);
        {
          PUSH_EXIT_FRAME();
          if (!ImplicitThisOperation(cx, state.obj0, state.name0, &state.res)) {
            goto error;
          }
        }
        PUSH(StackVal(state.res));
        END_OP(ImplicitThis);
      }

      case JSOp::CallSiteObj: {
        JSObject* cso = script->getObject(pc);
        MOZ_ASSERT(!cso->as<ArrayObject>().isExtensible());
        MOZ_ASSERT(cso->as<ArrayObject>().containsPure(
            frameMgr.cxForLocalUseOnly()->names().raw));
        PUSH(StackVal(ObjectValue(*cso)));
        END_OP(CallSiteObj);
      }

      case JSOp::IsConstructing: {
        PUSH(StackVal(MagicValue(JS_IS_CONSTRUCTING)));
        END_OP(IsConstructing);
      }

      case JSOp::SuperFun: {
        JSObject* superEnvFunc = &stack.pop().asValue().toObject();
        JSObject* superFun = SuperFunOperation(superEnvFunc);
        PUSH(StackVal(ObjectOrNullValue(superFun)));
        END_OP(SuperFun);
      }

      case JSOp::CheckThis:
      case JSOp::CheckThisReinit: {
        static_assert(JSOpLength_CheckThis == JSOpLength_CheckThisReinit);
        if (!stack[0].asValue().isMagic(JS_UNINITIALIZED_LEXICAL)) {
          PUSH_EXIT_FRAME();
          MOZ_ALWAYS_FALSE(ThrowInitializedThis(cx));
          goto error;
        }
        END_OP(CheckThis);
      }

      case JSOp::Generator: {
        JSObject* generator;
        {
          PUSH_EXIT_FRAME();
          generator = CreateGeneratorFromFrame(cx, frame);
          if (!generator) {
            goto error;
          }
        }
        PUSH(StackVal(ObjectValue(*generator)));
        END_OP(Generator);
      }

      case JSOp::InitialYield: {
        // gen => rval, gen, resumeKind
        state.obj0 = &stack[0].asValue().toObject();
        uint32_t frameSize = stack.frameSize(frame);
        {
          PUSH_EXIT_FRAME();
          if (!NormalSuspend(cx, state.obj0, frame, frameSize, pc)) {
            goto error;
          }
        }
        *ret = stack[0].asValue();
        stack.popFrame(frameMgr.cxForLocalUseOnly());
        stack.pop();  // fake return address
        return true;
      }

      case JSOp::Await:
      case JSOp::Yield: {
        // rval1, gen => rval2, gen, resumeKind
        state.obj0 = &stack[0].asValue().toObject();
        uint32_t frameSize = stack.frameSize(frame);
        {
          PUSH_EXIT_FRAME();
          if (!NormalSuspend(cx, state.obj0, frame, frameSize, pc)) {
            goto error;
          }
        }
        *ret = stack[0].asValue();
        stack.popFrame(frameMgr.cxForLocalUseOnly());
        stack.pop();  // fake return address
        return true;
      }

      case JSOp::FinalYieldRval: {
        // gen =>
        state.obj0 = &stack.pop().asValue().toObject();
        {
          PUSH_EXIT_FRAME();
          if (!FinalSuspend(cx, state.obj0, pc)) {
            goto error;
          }
        }
        stack.popFrame(frameMgr.cxForLocalUseOnly());
        stack.pop();  // fake return address
        return true;
      }

      case JSOp::IsGenClosing: {
        PUSH(StackVal(MagicValue(JS_GENERATOR_CLOSING)));
        END_OP(IsGenClosing);
      }

      case JSOp::AsyncAwait: {
        // value, gen => promise
        state.obj0 = &stack.pop().asValue().toObject();  // gen
        state.value0 = stack.pop().asValue();            // value
        JSObject* promise;
        {
          PUSH_EXIT_FRAME();
          promise = AsyncFunctionAwait(
              cx, state.obj0.as<AsyncFunctionGeneratorObject>(), state.value0);
          if (!promise) {
            goto error;
          }
        }
        PUSH(StackVal(ObjectValue(*promise)));
        END_OP(AsyncAwait);
      }

      case JSOp::AsyncResolve: {
        // valueOrReason, gen => promise
        state.obj0 = &stack.pop().asValue().toObject();  // gen
        state.value0 = stack.pop().asValue();            // valueOrReason
        auto resolveKind = AsyncFunctionResolveKind(GET_UINT8(pc));
        JSObject* promise;
        {
          PUSH_EXIT_FRAME();
          promise = AsyncFunctionResolve(
              cx, state.obj0.as<AsyncFunctionGeneratorObject>(), state.value0,
              resolveKind);
          if (!promise) {
            goto error;
          }
        }
        PUSH(StackVal(ObjectValue(*promise)));
        END_OP(AsyncResolve);
      }

      case JSOp::CanSkipAwait: {
        // value => value, can_skip
        state.value0 = stack[0].asValue();
        bool result = false;
        {
          PUSH_EXIT_FRAME();
          if (!CanSkipAwait(cx, state.value0, &result)) {
            goto error;
          }
        }
        PUSH(StackVal(BooleanValue(result)));
        END_OP(CanSkipAwait);
      }

      case JSOp::MaybeExtractAwaitValue: {
        // value, can_skip => value_or_resolved, can_skip
        state.value1 = stack.pop().asValue();  // can_skip
        state.value0 = stack.pop().asValue();  // value
        if (state.value1.toBoolean()) {
          PUSH_EXIT_FRAME();
          if (!ExtractAwaitValue(cx, state.value0, &state.value0)) {
            goto error;
          }
        }
        PUSH(StackVal(state.value0));
        PUSH(StackVal(state.value1));
        END_OP(MaybeExtractAwaitValue);
      }

      case JSOp::ResumeKind: {
        GeneratorResumeKind resumeKind = ResumeKindFromPC(pc);
        PUSH(StackVal(Int32Value(int32_t(resumeKind))));
        END_OP(ResumeKind);
      }

      case JSOp::CheckResumeKind: {
        // rval, gen, resumeKind => rval
        GeneratorResumeKind resumeKind =
            IntToResumeKind(stack.pop().asValue().toInt32());
        state.obj0 = &stack.pop().asValue().toObject();  // gen
        state.value0 = stack[0].asValue();               // rval
        if (resumeKind != GeneratorResumeKind::Next) {
          PUSH_EXIT_FRAME();
          MOZ_ALWAYS_FALSE(GeneratorThrowOrReturn(
              cx, frame, state.obj0.as<AbstractGeneratorObject>(), state.value0,
              resumeKind));
          goto error;
        }
        END_OP(CheckResumeKind);
      }

      case JSOp::Resume: {
        MOZ_CRASH("implement resume");
        END_OP(Resume);
      }

      case JSOp::JumpTarget: {
        int32_t icIndex = GET_INT32(pc);
        frame->interpreterICEntry() = frame->icScript()->icEntries() + icIndex;
        END_OP(JumpTarget);
      }
      case JSOp::LoopHead: {
        int32_t icIndex = GET_INT32(pc);
        frame->interpreterICEntry() = frame->icScript()->icEntries() + icIndex;
        END_OP(LoopHead);
      }
      case JSOp::AfterYield: {
        int32_t icIndex = GET_INT32(pc);
        frame->interpreterICEntry() = frame->icScript()->icEntries() + icIndex;
        END_OP(AfterYield);
      }

      case JSOp::Goto: {
        ADVANCE(GET_JUMP_OFFSET(pc));
        break;
      }

      case JSOp::Coalesce: {
        if (!stack[0].asValue().isNullOrUndefined()) {
          ADVANCE(GET_JUMP_OFFSET(pc));
          break;
        } else {
          END_OP(Coalesce);
        }
      }

      case JSOp::Case: {
        bool cond = stack.pop().asValue().toBoolean();
        if (cond) {
          stack.pop();
          ADVANCE(GET_JUMP_OFFSET(pc));
          break;
        } else {
          END_OP(Case);
        }
      }

      case JSOp::Default: {
        stack.pop();
        ADVANCE(GET_JUMP_OFFSET(pc));
        break;
      }

      case JSOp::TableSwitch: {
        int32_t len = GET_JUMP_OFFSET(pc);
        int32_t low = GET_JUMP_OFFSET(pc + 1 * JUMP_OFFSET_LEN);
        int32_t high = GET_JUMP_OFFSET(pc + 2 * JUMP_OFFSET_LEN);
        Value v = stack.pop().asValue();
        int32_t i = 0;
        if (v.isInt32()) {
          i = v.toInt32();
        } else if (!v.isDouble() ||
                   !mozilla::NumberEqualsInt32(v.toDouble(), &i)) {
          ADVANCE(len);
          break;
        }

        i = uint32_t(i) - uint32_t(low);
        if ((uint32_t(i) < uint32_t(high - low + 1))) {
          len = script->tableSwitchCaseOffset(pc, uint32_t(i)) -
                script->pcToOffset(pc);
        }
        ADVANCE(len);
        break;
      }

      case JSOp::Return: {
        *ret = stack.pop().asValue();
        stack.popFrame(frameMgr.cxForLocalUseOnly());
        stack.pop();  // fake return address
        return true;
      }

      case JSOp::GetRval: {
        PUSH(StackVal(*ret));
        END_OP(GetRval);
      }

      case JSOp::SetRval: {
        *ret = stack.pop().asValue();
        END_OP(SetRval);
      }

      case JSOp::RetRval: {
        stack.popFrame(frameMgr.cxForLocalUseOnly());
        stack.pop();  // fake return address
        return true;
      }

      case JSOp::CheckReturn: {
        Value thisval = stack.pop().asValue();
        if (ret->isObject()) {
          PUSH(StackVal(*ret));
        } else if (!ret->isUndefined()) {
          PUSH_EXIT_FRAME();
          state.value0 = *ret;
          ReportValueError(cx, JSMSG_BAD_DERIVED_RETURN, JSDVG_IGNORE_STACK,
                           state.value0, nullptr);
          goto error;
        } else if (thisval.isMagic(JS_UNINITIALIZED_LEXICAL)) {
          PUSH_EXIT_FRAME();
          MOZ_ALWAYS_FALSE(ThrowUninitializedThis(cx));
          goto error;
        } else {
          PUSH(StackVal(thisval));
        }
        END_OP(CheckReturn);
      }

      case JSOp::Throw: {
        state.value0 = stack.pop().asValue();
        {
          PUSH_EXIT_FRAME();
          MOZ_ALWAYS_FALSE(ThrowOperation(cx, state.value0));
          goto error;
        }
        END_OP(Throw);
      }

      case JSOp::ThrowMsg: {
        {
          PUSH_EXIT_FRAME();
          MOZ_ALWAYS_FALSE(ThrowMsgOperation(cx, GET_UINT8(pc)));
          goto error;
        }
        END_OP(ThrowMsg);
      }

      case JSOp::ThrowSetConst: {
        {
          PUSH_EXIT_FRAME();
          ReportRuntimeLexicalError(cx, JSMSG_BAD_CONST_ASSIGN, script, pc);
          goto error;
        }
        END_OP(ThrowSetConst);
      }

      case JSOp::Try:
      case JSOp::TryDestructuring: {
        static_assert(JSOpLength_Try == JSOpLength_TryDestructuring);
        END_OP(Try);
      }

      case JSOp::Exception: {
        {
          PUSH_EXIT_FRAME();
          if (!GetAndClearException(cx, &state.res)) {
            goto error;
          }
        }
        PUSH(StackVal(state.res));
        END_OP(Exception);
      }

      case JSOp::Finally: {
        END_OP(Finally);
      }

      case JSOp::Uninitialized: {
        PUSH(StackVal(MagicValue(JS_UNINITIALIZED_LEXICAL)));
        END_OP(Uninitialized);
      }
      case JSOp::InitLexical: {
        uint32_t i = GET_LOCALNO(pc);
        frame->unaliasedLocal(i) = stack[0].asValue();
        END_OP(InitLexical);
      }

      case JSOp::InitAliasedLexical: {
        EnvironmentCoordinate ec = EnvironmentCoordinate(pc);
        EnvironmentObject& obj = getEnvironmentFromCoordinate(frame, ec);
        obj.setAliasedBinding(ec, stack[0].asValue());
        END_OP(InitAliasedLexical);
      }
      case JSOp::CheckLexical: {
        if (stack[0].asValue().isMagic(JS_UNINITIALIZED_LEXICAL)) {
          PUSH_EXIT_FRAME();
          ReportRuntimeLexicalError(cx, JSMSG_UNINITIALIZED_LEXICAL, script,
                                    pc);
          goto error;
        }
        END_OP(CheckLexical);
      }
      case JSOp::CheckAliasedLexical: {
        if (stack[0].asValue().isMagic(JS_UNINITIALIZED_LEXICAL)) {
          PUSH_EXIT_FRAME();
          ReportRuntimeLexicalError(cx, JSMSG_UNINITIALIZED_LEXICAL, script,
                                    pc);
          goto error;
        }
        END_OP(CheckAliasedLexical);
      }

      case JSOp::BindGName: {
        IC_SET_OBJ_ARG(
            0, &frameMgr.cxForLocalUseOnly()->global()->lexicalEnvironment());
        state.name0.set(script->getName(pc));
        INVOKE_IC(BindName);
        IC_PUSH_RESULT();
        END_OP(BindGName);
      }
      case JSOp::BindName: {
        IC_SET_OBJ_ARG(0, frame->environmentChain());
        INVOKE_IC(BindName);
        IC_PUSH_RESULT();
        END_OP(BindName);
      }
      case JSOp::GetGName: {
        IC_SET_OBJ_ARG(
            0, &frameMgr.cxForLocalUseOnly()->global()->lexicalEnvironment());
        INVOKE_IC(GetName);
        IC_PUSH_RESULT();
        END_OP(GetGName);
      }
      case JSOp::GetName: {
        IC_SET_OBJ_ARG(0, frame->environmentChain());
        INVOKE_IC(GetName);
        IC_PUSH_RESULT();
        END_OP(GetName);
      }

      case JSOp::GetArg: {
        unsigned i = GET_ARGNO(pc);
        if (script->argsObjAliasesFormals()) {
          PUSH(StackVal(frame->argsObj().arg(i)));
        } else {
          PUSH(StackVal(frame->unaliasedFormal(i)));
        }
        END_OP(GetArg);
      }

      case JSOp::GetFrameArg: {
        uint32_t i = GET_ARGNO(pc);
        PUSH(StackVal(frame->unaliasedFormal(i, DONT_CHECK_ALIASING)));
        END_OP(GetFrameArg);
      }

      case JSOp::GetLocal: {
        uint32_t i = GET_LOCALNO(pc);
        TRACE_PRINTF(" -> local: %d\n", int(i));
        PUSH(StackVal(frame->unaliasedLocal(i)));
        END_OP(GetLocal);
      }

      case JSOp::ArgumentsLength: {
        PUSH(StackVal(Int32Value(frame->numActualArgs())));
        END_OP(ArgumentsLength);
      }

      case JSOp::GetActualArg: {
        MOZ_ASSERT(!script->needsArgsObj());
        uint32_t index = stack[0].asValue().toInt32();
        stack[0] = StackVal(frame->unaliasedActual(index));
        END_OP(GetActualArg);
      }

      case JSOp::GetAliasedVar:
      case JSOp::GetAliasedDebugVar: {
        static_assert(JSOpLength_GetAliasedVar ==
                      JSOpLength_GetAliasedDebugVar);
        EnvironmentCoordinate ec = EnvironmentCoordinate(pc);
        EnvironmentObject& obj = getEnvironmentFromCoordinate(frame, ec);
        PUSH(StackVal(obj.aliasedBinding(ec)));
        END_OP(GetAliasedVar);
      }

      case JSOp::GetImport: {
        state.obj0 = frame->environmentChain();
        state.value0 = stack[0].asValue();
        {
          PUSH_EXIT_FRAME();
          if (!GetImportOperation(cx, state.obj0, script, pc, &state.value0)) {
            goto error;
          }
        }
        stack[0] = StackVal(state.value0);
        END_OP(GetImport);
      }

      case JSOp::GetIntrinsic: {
        INVOKE_IC(GetIntrinsic);
        IC_PUSH_RESULT();
        END_OP(GetIntrinsic);
      }

      case JSOp::Callee: {
        PUSH(StackVal(frame->calleev()));
        END_OP(Callee);
      }

      case JSOp::EnvCallee: {
        uint8_t numHops = GET_UINT8(pc);
        JSObject* env = &frame->environmentChain()->as<EnvironmentObject>();
        for (unsigned i = 0; i < numHops; i++) {
          env = &env->as<EnvironmentObject>().enclosingEnvironment();
        }
        PUSH(StackVal(ObjectValue(env->as<CallObject>().callee())));
        END_OP(EnvCallee);
      }

      case JSOp::SetProp:
      case JSOp::StrictSetProp:
      case JSOp::SetName:
      case JSOp::StrictSetName:
      case JSOp::SetGName:
      case JSOp::StrictSetGName: {
        static_assert(JSOpLength_SetProp == JSOpLength_StrictSetProp);
        static_assert(JSOpLength_SetProp == JSOpLength_SetName);
        static_assert(JSOpLength_SetProp == JSOpLength_StrictSetName);
        static_assert(JSOpLength_SetProp == JSOpLength_SetGName);
        static_assert(JSOpLength_SetProp == JSOpLength_StrictSetGName);
        IC_POP_ARG(1);
        IC_POP_ARG(0);
        PUSH(StackVal(state.icVals[1]));
        INVOKE_IC(SetProp);
        END_OP(SetProp);
      }

      case JSOp::InitProp:
      case JSOp::InitHiddenProp:
      case JSOp::InitLockedProp: {
        static_assert(JSOpLength_InitProp == JSOpLength_InitHiddenProp);
        static_assert(JSOpLength_InitProp == JSOpLength_InitLockedProp);
        IC_POP_ARG(1);
        IC_SET_ARG_FROM_STACK(0, 0);
        INVOKE_IC(SetProp);
        END_OP(InitProp);
      }
      case JSOp::InitGLexical: {
        IC_SET_ARG_FROM_STACK(1, 0);
        IC_SET_OBJ_ARG(
            0, &frameMgr.cxForLocalUseOnly()->global()->lexicalEnvironment());
        INVOKE_IC(SetProp);
        END_OP(InitGLexical);
      }

      case JSOp::SetArg: {
        unsigned i = GET_ARGNO(pc);
        if (script->argsObjAliasesFormals()) {
          frame->argsObj().setArg(i, stack[0].asValue());
        } else {
          frame->unaliasedFormal(i) = stack[0].asValue();
        }
        END_OP(SetArg);
      }

      case JSOp::SetLocal: {
        uint32_t i = GET_LOCALNO(pc);
        TRACE_PRINTF(" -> local: %d\n", int(i));
        frame->unaliasedLocal(i) = stack[0].asValue();
        END_OP(SetLocal);
      }

      case JSOp::SetAliasedVar: {
        EnvironmentCoordinate ec = EnvironmentCoordinate(pc);
        EnvironmentObject& obj = getEnvironmentFromCoordinate(frame, ec);
        MOZ_ASSERT(!IsUninitializedLexical(obj.aliasedBinding(ec)));
        obj.setAliasedBinding(ec, stack[0].asValue());
        END_OP(SetAliasedVar);
      }

      case JSOp::SetIntrinsic: {
        state.value0 = stack[0].asValue();
        {
          PUSH_EXIT_FRAME();
          if (!SetIntrinsicOperation(cx, script, pc, state.value0)) {
            goto error;
          }
        }
        END_OP(SetIntrinsic);
      }

      case JSOp::PushLexicalEnv: {
        state.scope0 = script->getScope(pc);
        {
          PUSH_EXIT_FRAME();
          if (!frame->pushLexicalEnvironment(cx,
                                             state.scope0.as<LexicalScope>())) {
            goto error;
          }
        }
        END_OP(PushLexicalEnv);
      }
      case JSOp::PopLexicalEnv: {
        frame->popOffEnvironmentChain<LexicalEnvironmentObject>();
        END_OP(PopLexicalEnv);
      }
      case JSOp::DebugLeaveLexicalEnv: {
        END_OP(DebugLeaveLexicalEnv);
      }

      case JSOp::RecreateLexicalEnv: {
        {
          PUSH_EXIT_FRAME();
          if (!frame->recreateLexicalEnvironment(cx)) {
            goto error;
          }
        }
        END_OP(RecreateLexicalEnv);
      }

      case JSOp::FreshenLexicalEnv: {
        {
          PUSH_EXIT_FRAME();
          if (!frame->freshenLexicalEnvironment(cx)) {
            goto error;
          }
        }
        END_OP(FreshenLexicalEnv);
      }
      case JSOp::PushClassBodyEnv: {
        state.scope0 = script->getScope(pc);
        {
          PUSH_EXIT_FRAME();
          if (!frame->pushClassBodyEnvironment(
                  cx, state.scope0.as<ClassBodyScope>())) {
            goto error;
          }
        }
        END_OP(PushClassBodyEnv);
      }
      case JSOp::PushVarEnv: {
        state.scope0 = script->getScope(pc);
        {
          PUSH_EXIT_FRAME();
          if (!frame->pushVarEnvironment(cx, state.scope0)) {
            goto error;
          }
        }
        END_OP(PushVarEnv);
      }
      case JSOp::EnterWith: {
        state.scope0 = script->getScope(pc);
        state.value0 = stack.pop().asValue();
        {
          PUSH_EXIT_FRAME();
          if (!EnterWithOperation(cx, frame, state.value0,
                                  state.scope0.as<WithScope>())) {
            goto error;
          }
        }
        END_OP(EnterWith);
      }
      case JSOp::LeaveWith: {
        frame->popOffEnvironmentChain<WithEnvironmentObject>();
        END_OP(LeaveWith);
      }
      case JSOp::BindVar: {
        state.obj0 = frame->environmentChain();
        JSObject* varObj;
        {
          PUSH_EXIT_FRAME();
          varObj = BindVarOperation(cx, state.obj0);
        }
        PUSH(StackVal(ObjectValue(*varObj)));
        END_OP(BindVar);
      }

      case JSOp::GlobalOrEvalDeclInstantiation: {
        GCThingIndex lastFun = GET_GCTHING_INDEX(pc);
        state.script0 = script;
        state.obj0 = frame->environmentChain();
        {
          PUSH_EXIT_FRAME();
          if (!GlobalOrEvalDeclInstantiation(cx, state.obj0, state.script0,
                                             lastFun)) {
            goto error;
          }
        }
        END_OP(GlobalOrEvalDeclInstantiation);
      }

      case JSOp::DelName: {
        state.name0 = script->getName(pc);
        state.obj0 = frame->environmentChain();
        {
          PUSH_EXIT_FRAME();
          if (!DeleteNameOperation(cx, state.name0, state.obj0, &state.res)) {
            goto error;
          }
        }
        PUSH(StackVal(state.res));
        END_OP(DelName);
      }

      case JSOp::Arguments: {
        {
          PUSH_EXIT_FRAME();
          if (!NewArgumentsObject(cx, frame, &state.res)) {
            goto error;
          }
        }
        PUSH(StackVal(state.res));
        END_OP(Arguments);
      }

      case JSOp::Rest: {
        INVOKE_IC(Rest);
        IC_PUSH_RESULT();
        END_OP(Rest);
      }

      case JSOp::FunctionThis: {
        {
          PUSH_EXIT_FRAME();
          if (!js::GetFunctionThis(cx, frame, &state.res)) {
            goto error;
          }
        }
        PUSH(StackVal(state.res));
        END_OP(FunctionThis);
      }

      case JSOp::Pop: {
        stack.pop();
        END_OP(Pop);
      }
      case JSOp::PopN: {
        uint32_t n = GET_UINT16(pc);
        stack.popn(n);
        END_OP(PopN);
      }
      case JSOp::Dup: {
        StackVal value = stack[0];
        PUSH(value);
        END_OP(Dup);
      }
      case JSOp::Dup2: {
        StackVal value1 = stack[0];
        StackVal value2 = stack[1];
        PUSH(value2);
        PUSH(value1);
        END_OP(Dup2);
      }
      case JSOp::DupAt: {
        unsigned i = GET_UINT24(pc);
        StackVal value = stack[i];
        PUSH(value);
        END_OP(DupAt);
      }
      case JSOp::Swap: {
        std::swap(stack[0], stack[1]);
        END_OP(Swap);
      }
      case JSOp::Pick: {
        unsigned i = GET_UINT8(pc);
        StackVal tmp = stack[i];
        memmove(&stack[1], &stack[0], sizeof(StackVal) * i);
        stack[0] = tmp;
        END_OP(Pick);
      }
      case JSOp::Unpick: {
        unsigned i = GET_UINT8(pc);
        StackVal tmp = stack[0];
        memmove(&stack[0], &stack[1], sizeof(StackVal) * i);
        stack[i] = tmp;
        END_OP(Unpick);
      }
      case JSOp::DebugCheckSelfHosted: {
        END_OP(DebugCheckSelfHosted);
      }
      case JSOp::Lineno: {
        END_OP(Lineno);
      }
      case JSOp::NopDestructuring: {
        END_OP(NopDestructuring);
      }
      case JSOp::ForceInterpreter: {
        END_OP(ForceInterpreter);
      }
      case JSOp::Debugger: {
        END_OP(Debugger);
      }

      default:
        MOZ_CRASH("Bad opcode");
    }
  }

error:
  TRACE_PRINTF("HandleException\n");
  do {
    ResumeFromException rfe;
    {
      PUSH_EXIT_FRAME();
      HandleException(&rfe);
    }

    switch (rfe.kind) {
      case ExceptionResumeKind::EntryFrame:
        TRACE_PRINTF(" -> Return from entry frame\n");
        *ret = MagicValue(JS_ION_ERROR);
        stack.popFrame(frameMgr.cxForLocalUseOnly());
        stack.pop();  // fake return address
        return false;
      case ExceptionResumeKind::Catch:
        pc = frame->interpreterPC();
        TRACE_PRINTF(" -> catch to pc %p\n", pc);
        goto dispatch;
      case ExceptionResumeKind::Finally:
        pc = frame->interpreterPC();
        TRACE_PRINTF(" -> finally to pc %p\n", pc);
        PUSH(StackVal(rfe.exception));
        PUSH(StackVal(BooleanValue(true)));
        goto dispatch;
      case ExceptionResumeKind::ForcedReturnBaseline:
        TRACE_PRINTF(" -> forced return\n");
        stack.popFrame(frameMgr.cxForLocalUseOnly());
        stack.pop();  // fake return address
        return true;
        break;
      case ExceptionResumeKind::ForcedReturnIon:
        MOZ_CRASH(
            "Unexpected ForcedReturnIon exception-resume kind in Portable "
            "Baseline");
      case ExceptionResumeKind::Bailout:
        MOZ_CRASH(
            "Unexpected Bailout exception-resume kind in Portable Baseline");
      case ExceptionResumeKind::Wasm:
        MOZ_CRASH("Unexpected Wasm exception-resume kind in Portable Baseline");
      case ExceptionResumeKind::WasmCatch:
        MOZ_CRASH(
            "Unexpected WasmCatch exception-resume kind in Portable "
            "Baseline");
    }
  } while (false);

  goto dispatch;
}

bool js::PortableBaselineTrampoline(JSContext* cx, size_t argc, Value* argv,
                                    size_t numActualArgs,
                                    CalleeToken calleeToken, JSObject* envChain,
                                    Value* result) {
  Stack stack(cx->portableBaselineStack());

  // Expected stack frame:
  // - argN
  // - ...
  // - arg1
  // - this
  // - calleeToken
  // - descriptor
  // - "return address" (nullptr for top frame)

  if (CalleeTokenIsConstructing(calleeToken)) {
    argc++;
  }
  for (size_t i = 0; i < argc; i++) {
    PUSH(StackVal(argv[argc - 1 - i]));
  }
  PUSH(StackVal(calleeToken));
  PUSH(StackVal(
      MakeFrameDescriptorForJitCall(FrameType::CppToJSJit, numActualArgs)));
  PUSH(StackVal(nullptr));  // Fake return address.

  if (!PortableBaselineInterpret(cx, stack, envChain, result)) {
    return false;
  }

  // Pop the descriptor, calleeToken, and args. (Return address is
  // popped in callee.)
  stack.popn(2 + argc);

  return true;
}

MethodStatus js::CanEnterPortableBaselineInterpreter(JSContext* cx,
                                                     RunState& state) {
  if (!JitOptions.portableBaselineInterpreter) {
    return MethodStatus::Method_CantCompile;
  }
  if (state.script()->hasJitScript()) {
    return MethodStatus::Method_Compiled;
  }
  if (state.script()->hasForceInterpreterOp()) {
    return MethodStatus::Method_CantCompile;
  }
  if (state.script()->nslots() > BaselineMaxScriptSlots) {
    return MethodStatus::Method_CantCompile;
  }
  if (state.isInvoke()) {
    InvokeState& invoke = *state.asInvoke();
    if (TooManyActualArguments(invoke.args().length())) {
      return MethodStatus::Method_CantCompile;
    }
  }
  if (state.script()->getWarmUpCount() <=
      JitOptions.portableBaselineInterpreterWarmUpThreshold) {
    return MethodStatus::Method_Skipped;
  }
  if (!cx->realm()->ensureJitRealmExists(cx)) {
    return MethodStatus::Method_Error;
  }

  AutoKeepJitScripts keepJitScript(cx);
  if (!state.script()->ensureHasJitScript(cx, keepJitScript)) {
    return MethodStatus::Method_Error;
  }
  state.script()->updateJitCodeRaw(cx->runtime());
  return MethodStatus::Method_Compiled;
}
