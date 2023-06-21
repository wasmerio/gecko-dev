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

#include "jit/BaselineFrame.h"
#include "jit/BaselineIC.h"
#include "jit/BaselineJIT.h"
#include "jit/CacheIR.h"
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

#include "jit/BaselineFrame-inl.h"
#include "jit/JitScript-inl.h"
#include "vm/EnvironmentObject-inl.h"
#include "vm/Interpreter-inl.h"
#include "vm/JSScript-inl.h"

#define TRACE_INTERP

using namespace js;
using namespace js::jit;

struct StackValue {
  uint64_t value;

  explicit StackValue(uint64_t v) : value(v) {}
  explicit StackValue(Value v) : value(v.asRawBits()) {}
  explicit StackValue(void* v) : value(reinterpret_cast<uint64_t>(v)) {}

  uint64_t asUInt64() const { return value; }
  Value asValue() const { return Value::fromRawBits(value); }
  void* asVoidPtr() const { return reinterpret_cast<void*>(value); }
  CalleeToken asCalleeToken() const {
    return reinterpret_cast<CalleeToken>(value);
  }
};

struct Stack {
  StackValue** sp;
  StackValue* fp;
  StackValue* base;
  StackValue* top;

  Stack(PortableBaselineStack& pbs)
      : sp(reinterpret_cast<StackValue**>(&pbs.top)),
        fp(nullptr),
        base(reinterpret_cast<StackValue*>(pbs.base)),
        top(reinterpret_cast<StackValue*>(pbs.top)) {}

  [[nodiscard]] StackValue* allocate(size_t size) {
    if (reinterpret_cast<uintptr_t>(base) + size >
        reinterpret_cast<uintptr_t>(*sp)) {
      return nullptr;
    }
    (*sp) =
        reinterpret_cast<StackValue*>(reinterpret_cast<uintptr_t>(*sp) - size);
    return *sp;
  }

  [[nodiscard]] bool push(StackValue v) {
    StackValue* elem = allocate(sizeof(StackValue));
    if (!elem) {
      return false;
    }
    *elem = v;
    return true;
  }
  StackValue pop() {
    MOZ_ASSERT((*sp) + 1 <= top);
    return *(*sp)++;
  }
  void popn(size_t len) {
    MOZ_ASSERT((*sp) + len <= top);
    (*sp) += len;
  }

  StackValue* cur() const { return *sp; }
  void restore(StackValue* s) { *sp = s; }

  uint32_t frameSize(BaselineFrame* curFrame) const {
    return sizeof(StackValue) * (reinterpret_cast<StackValue*>(fp) - cur());
  }

  [[nodiscard]] BaselineFrame* pushFrame(JSContext* cx, JSObject* envChain) {
    auto* prevFP = fp;
    if (!push(StackValue(fp))) {
      return nullptr;
    }
    fp = cur();

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
    uintptr_t frameSize =
        reinterpret_cast<uintptr_t>(prevFP) - reinterpret_cast<uintptr_t>(fp);
    frame->setDebugFrameSize(frameSize);
#endif
    return frame;
  }

  void popFrame(JSContext* cx) {
    StackValue* newTOS = fp + 1;
    fp = reinterpret_cast<StackValue*>(fp->asVoidPtr());
    restore(newTOS);
  }

  [[nodiscard]] StackValue* pushExitFrame(BaselineFrame* prevFrame) {
    uint8_t* prevFP =
        reinterpret_cast<uint8_t*>(prevFrame) + BaselineFrame::Size();

    if (!push(StackValue(
            MakeFrameDescriptorForJitCall(FrameType::BaselineJS, 0)))) {
      return nullptr;
    }
    if (!push(StackValue(nullptr))) {  // fake return address.
      return nullptr;
    }
    if (!push(StackValue(prevFP))) {
      return nullptr;
    }
    StackValue* exitFP = cur();
    if (!push(StackValue(uint64_t(ExitFrameType::Bare)))) {
      return nullptr;
    }
#ifdef DEBUG
    uintptr_t frameSize =
        (reinterpret_cast<uintptr_t>(prevFP) -
         reinterpret_cast<uintptr_t>(exitFP) - ExitFrameLayout::Size());
    MOZ_ASSERT(frameSize <= 0xffffffff);
    prevFrame->setDebugFrameSize(uint32_t(frameSize));
#endif
    return exitFP;
  }

  void popExitFrame(StackValue* fp) {
    restore(fp);
    (*sp) += 3;
  }

  BaselineFrame* frameFromFP() {
    return reinterpret_cast<BaselineFrame*>(reinterpret_cast<uintptr_t>(fp) -
                                            BaselineFrame::Size());
  }

  StackValue& operator[](size_t index) { return (*sp)[index]; }
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
  RootedScript script0;
  Rooted<PropertyName*> name0;
  Rooted<jsid> id0;
  Rooted<JSAtom*> atom0;
  RootedFunction fun0;
  Rooted<Scope*> scope0;
  JSOp op;
  int argc;
  int extraArgs;
  bool spreadCall;
  int32_t jumpOffset;
  ICStub* stub;
  void* fallbackIC;
  void* stubTail;
  mozilla::Maybe<CacheIRReader> cacheIRReader;

  State(JSContext* cx)
      : value0(cx),
        value1(cx),
        value2(cx),
        value3(cx),
        res(cx),
        obj0(cx),
        obj1(cx),
        obj2(cx),
        script0(cx),
        name0(cx),
        id0(cx),
        atom0(cx),
        fun0(cx),
        scope0(cx) {}
};

struct PC {
  jsbytecode* pc;

  explicit PC(BaselineFrame* frame) : pc(frame->interpreterPC()) {}

  void advance(BaselineFrame* frame, intptr_t delta) { pc += delta; }
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
  StackValue* exitFP;

 public:
  VMFrame(VMFrameManager& mgr, Stack& stack_) : cx(mgr.cx), stack(stack_) {
    prevExitFP = cx->activation()->asJit()->packedExitFP();
    exitFP = stack.pushExitFrame(mgr.frame);
    if (exitFP) {
      cx->activation()->asJit()->setJSExitFP(
          reinterpret_cast<uint8_t*>(exitFP));
    }
  }

  ~VMFrame() {
    cx->activation()->asJit()->setPackedExitFP(prevExitFP);
    stack.popExitFrame(exitFP);
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

// TODO: check all stack pushes for overflow
// TODO: convert all (except OOM) `return false`s into exception-handling path
// TODO: VM-call frames around ICs (and calls into runtime?) Mechanism
// in general surrounding "escapes"; use this to cache SP, PC as well.

#define TRY(x)    \
  if (!(x)) {     \
    return false; \
  }

#define PUSH(val) TRY(stack.push(val));

static bool PortableBaselineInterpret(JSContext* cx_, Stack& stack,
                                      JSObject* envChain, Value* ret) {
  State state(cx_);

  TRY(stack.pushFrame(cx_, envChain));

  BaselineFrame* frame = stack.frameFromFP();
  RootedScript script(cx_, frame->script());
  PC pc(frame);

  uint32_t nslots = script->nslots();
  for (uint32_t i = 0; i < nslots; i++) {
    TRY(stack.push(StackValue(UndefinedValue())));
  }
  ret->setUndefined();

  if (CalleeTokenIsFunction(frame->calleeToken())) {
    JSFunction* func = CalleeTokenToFunction(frame->calleeToken());
    frame->setEnvironmentChain(func->environment());
    if (func->needsFunctionEnvironmentObjects()) {
      TRY(js::InitFunctionEnvironmentObjects(cx_, frame));
    }
  }

  VMFrameManager frameMgr(cx_, frame);

  while (true) {
  dispatch:
    frame->interpreterPC() = pc.pc;

#define ADVANCE(delta) pc.advance(frame, (delta));
#define ADVANCE_AND_DISPATCH(delta) \
  ADVANCE(delta);                   \
  goto dispatch;
#define NEXT_IC() frame->interpreterICEntry()++;

#define END_OP(op) ADVANCE_AND_DISPATCH(JSOpLength_##op);

#define PUSH_EXIT_FRAME()      \
  VMFrame cx(frameMgr, stack); \
  if (!cx.success()) {         \
    return false;              \
  }

    state.op = JSOp(*pc.pc);

#ifdef TRACE_INTERP
    printf("stack[0] = %" PRIx64 " stack[1] = %" PRIx64 " stack[2] = %" PRIx64
           "\n",
           stack[0].asUInt64(), stack[1].asUInt64(), stack[2].asUInt64());
    printf("script = %p pc = %p: %s (ic %d) pending = %d\n", script.get(),
           pc.pc, CodeName(state.op),
           (int)(frame->interpreterICEntry() -
                 script->jitScript()->icScript()->icEntries()),
           frameMgr.cxForLocalUseOnly()->isExceptionPending());
    fflush(stdout);
#endif

    switch (state.op) {
      case JSOp::Nop: {
        END_OP(Nop);
      }
      case JSOp::Undefined: {
        PUSH(StackValue(UndefinedValue()));
        END_OP(Undefined);
      }
      case JSOp::Null: {
        PUSH(StackValue(NullValue()));
        END_OP(Null);
      }
      case JSOp::False: {
        PUSH(StackValue(BooleanValue(false)));
        END_OP(False);
      }
      case JSOp::True: {
        PUSH(StackValue(BooleanValue(true)));
        END_OP(True);
      }
      case JSOp::Int32: {
        PUSH(StackValue(Int32Value(GET_INT32(pc.pc))));
        END_OP(Int32);
      }
      case JSOp::Zero: {
        PUSH(StackValue(Int32Value(0)));
        END_OP(Zero);
      }
      case JSOp::One: {
        PUSH(StackValue(Int32Value(1)));
        END_OP(One);
      }
      case JSOp::Int8: {
        PUSH(StackValue(Int32Value(GET_INT8(pc.pc))));
        END_OP(Int8);
      }
      case JSOp::Uint16: {
        PUSH(StackValue(Int32Value(GET_UINT16(pc.pc))));
        END_OP(Uint16);
      }
      case JSOp::Uint24: {
        PUSH(StackValue(Int32Value(GET_UINT24(pc.pc))));
        END_OP(Uint24);
      }
      case JSOp::Double: {
        PUSH(StackValue(GET_INLINE_VALUE(pc.pc)));
        END_OP(Double);
      }
      case JSOp::BigInt: {
        PUSH(StackValue(JS::BigIntValue(script->getBigInt(pc.pc))));
        END_OP(BigInt);
      }
      case JSOp::String: {
        PUSH(StackValue(StringValue(script->getString(pc.pc))));
        END_OP(String);
      }
      case JSOp::Symbol: {
        PUSH(StackValue(
            SymbolValue(frameMgr.cxForLocalUseOnly()->wellKnownSymbols().get(
                GET_UINT8(pc.pc)))));
        END_OP(Symbol);
      }
      case JSOp::Void: {
        stack[0] = StackValue(JS::UndefinedValue());
        END_OP(Void);
      }

      case JSOp::Typeof:
      case JSOp::TypeofExpr: {
        static_assert(JSOpLength_Typeof == JSOpLength_TypeofExpr);
        ADVANCE(JSOpLength_Typeof);
        state.value0 = stack.pop().asValue();
        goto ic_Typeof;
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
        ADVANCE(JSOpLength_Pos);
        state.value0 = stack.pop().asValue();
        goto ic_UnaryArith;
      }
      case JSOp::Not: {
        ADVANCE(JSOpLength_Not);
        state.value0 = stack.pop().asValue();
        goto ic_ToBool;
      }
      case JSOp::And:
      case JSOp::Or: {
        static_assert(JSOpLength_And == JSOpLength_Or);
        state.jumpOffset = GET_JUMP_OFFSET(pc.pc) - JSOpLength_And;
        ADVANCE(JSOpLength_And);
        state.value0 = stack[0].asValue();
        goto ic_ToBool;
      }
      case JSOp::JumpIfTrue:
      case JSOp::JumpIfFalse: {
        static_assert(JSOpLength_JumpIfTrue == JSOpLength_JumpIfFalse);
        state.jumpOffset = GET_JUMP_OFFSET(pc.pc) - JSOpLength_JumpIfTrue;
        ADVANCE(JSOpLength_JumpIfTrue);
        state.value0 = stack.pop().asValue();
        goto ic_ToBool;
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
        state.value1 = stack.pop().asValue();
        state.value0 = stack.pop().asValue();
        ADVANCE(JSOpLength_Div);
        goto ic_BinaryArith;
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
        state.value1 = stack.pop().asValue();
        state.value0 = stack.pop().asValue();
        ADVANCE(JSOpLength_Eq);
        goto ic_Compare;
      }

      case JSOp::Instanceof: {
        state.value1 = stack.pop().asValue();
        state.value0 = stack.pop().asValue();
        ADVANCE(JSOpLength_Instanceof);
        goto ic_InstanceOf;
      }

      case JSOp::In: {
        state.value1 = stack.pop().asValue();
        state.value0 = stack.pop().asValue();
        ADVANCE(JSOpLength_In);
        goto ic_In;
      }

      case JSOp::ToPropertyKey: {
        state.value0 = stack.pop().asValue();
        ADVANCE(JSOpLength_ToPropertyKey);
        goto ic_ToPropertyKey;
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
        PUSH(StackValue(StringValue(result)));
        END_OP(ToString);
      }

      case JSOp::IsNullOrUndefined: {
        bool result =
            stack[0].asValue().isNull() || stack[0].asValue().isUndefined();
        stack[0] = StackValue(BooleanValue(result));
        END_OP(IsNullOrUndefined);
      }

      case JSOp::GlobalThis: {
        PUSH(StackValue(ObjectValue(*frameMgr.cxForLocalUseOnly()
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
        PUSH(StackValue(state.value0));
        END_OP(NonSyntacticGlobalThis);
      }

      case JSOp::NewTarget: {
        PUSH(StackValue(frame->newTarget()));
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
        PUSH(StackValue(ObjectValue(*promise)));
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
        PUSH(StackValue(ObjectValue(*metaObject)));
        END_OP(ImportMeta);
      }

      case JSOp::NewInit: {
        ADVANCE(JSOpLength_NewInit);
        goto ic_NewObject;
      }
      case JSOp::NewObject: {
        ADVANCE(JSOpLength_NewObject);
        goto ic_NewObject;
      }
      case JSOp::Object: {
        PUSH(StackValue(ObjectValue(*script->getObject(pc.pc))));
        END_OP(Object);
      }
      case JSOp::ObjWithProto: {
        state.value0 = stack[0].asValue();
        JSObject* obj;
        {
          PUSH_EXIT_FRAME();
          obj = ObjectWithProtoOperation(cx, state.value0);
        }
        stack[0] = StackValue(ObjectValue(*obj));
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
        state.value2 = stack.pop().asValue();
        state.value1 = stack.pop().asValue();
        state.value0 = stack[0].asValue();
        if (state.op == JSOp::InitElemInc) {
          PUSH(StackValue(Int32Value(state.value1.toInt32() + 1)));
        }
        ADVANCE(JSOpLength_InitElem);
        goto ic_SetElem;
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
        state.name0 = script->getName(pc.pc);
        {
          PUSH_EXIT_FRAME();
          if (!InitPropGetterSetterOperation(cx, pc.pc, state.obj0, state.name0,
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
          if (!InitElemGetterSetterOperation(cx, pc.pc, state.obj0,
                                             state.value0, state.obj1)) {
            goto error;
          }
        }
        END_OP(InitElemGetter);
      }

      case JSOp::GetProp:
      case JSOp::GetBoundName: {
        static_assert(JSOpLength_GetProp == JSOpLength_GetBoundName);
        state.value0 = stack.pop().asValue();
        ADVANCE(JSOpLength_GetProp);
        goto ic_GetProp;
      }
      case JSOp::GetPropSuper: {
        state.value1 = stack.pop().asValue();
        state.value0 = stack.pop().asValue();
        ADVANCE(JSOpLength_GetPropSuper);
        goto ic_GetPropSuper;
      }

      case JSOp::GetElem: {
        state.value1 = stack.pop().asValue();
        state.value0 = stack.pop().asValue();
        ADVANCE(JSOpLength_GetElem);
        goto ic_GetElem;
      }

      case JSOp::GetElemSuper: {
        state.value2 = stack.pop().asValue();
        state.value1 = stack.pop().asValue();
        state.value0 = stack.pop().asValue();
        ADVANCE(JSOpLength_GetElemSuper);
        goto ic_GetElemSuper;
      }

      case JSOp::DelProp: {
        state.value0 = stack.pop().asValue();
        state.name0 = script->getName(pc.pc);
        bool res = false;
        {
          PUSH_EXIT_FRAME();
          if (!DelPropOperation<true>(cx, state.value0, state.name0, &res)) {
            goto error;
          }
        }
        PUSH(StackValue(BooleanValue(res)));
        END_OP(DelProp);
      }
      case JSOp::StrictDelProp: {
        state.value0 = stack.pop().asValue();
        state.name0 = script->getName(pc.pc);
        bool res = false;
        {
          PUSH_EXIT_FRAME();
          if (!DelPropOperation<true>(cx, state.value0, state.name0, &res)) {
            goto error;
          }
        }
        PUSH(StackValue(BooleanValue(res)));
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
        PUSH(StackValue(BooleanValue(res)));
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
        PUSH(StackValue(BooleanValue(res)));
        END_OP(StrictDelElem);
      }

      case JSOp::HasOwn: {
        state.value1 = stack.pop().asValue();
        state.value0 = stack.pop().asValue();
        ADVANCE(JSOpLength_HasOwn);
        goto ic_HasOwn;
      }

      case JSOp::CheckPrivateField: {
        state.value1 = stack[1].asValue();
        state.value0 = stack[0].asValue();
        ADVANCE(JSOpLength_CheckPrivateField);
        goto ic_CheckPrivateField;
      }

      case JSOp::NewPrivateName: {
        state.atom0 = script->getAtom(pc.pc);
        JS::Symbol* symbol;
        {
          PUSH_EXIT_FRAME();
          symbol = NewPrivateName(cx, state.atom0);
          if (!symbol) {
            goto error;
          }
        }
        PUSH(StackValue(SymbolValue(symbol)));
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

        PUSH(StackValue(ObjectOrNullValue(superBase)));
        END_OP(SuperBase);
      }

      case JSOp::SetPropSuper:
      case JSOp::StrictSetPropSuper: {
        // stack signature: receiver, lval, rval => rval
        static_assert(JSOpLength_SetPropSuper == JSOpLength_StrictSetPropSuper);
        bool strict = state.op == JSOp::StrictSetPropSuper;
        state.value2 = stack.pop().asValue();  // rval
        state.value1 = stack.pop().asValue();  // lval
        state.value0 = stack.pop().asValue();  // receiver
        state.name0 = script->getName(pc.pc);
        {
          PUSH_EXIT_FRAME();
          // SetPropertySuper(cx, lval, receiver, name, rval, strict)
          // (N.B.: lval and receiver are transposed!)
          if (!SetPropertySuper(cx, state.value1, state.value0, state.name0,
                                state.value2, strict)) {
            goto error;
          }
        }
        PUSH(StackValue(state.value2));
        END_OP(SetPropSuper);
      }

      case JSOp::SetElemSuper:
      case JSOp::StrictSetElemSuper: {
        // stack signature: receiver, key, lval, rval => rval
        static_assert(JSOpLength_SetElemSuper == JSOpLength_StrictSetElemSuper);
        bool strict = state.op == JSOp::StrictSetElemSuper;
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
        PUSH(StackValue(state.value2));  // value
        END_OP(SetElemSuper);
      }

      case JSOp::Iter: {
        state.value0 = stack.pop().asValue();
        ADVANCE(JSOpLength_Iter);
        goto ic_GetIterator;
      }

      case JSOp::MoreIter: {
        // iter => iter, name
        Value v = IteratorMore(&stack[0].asValue().toObject());
        PUSH(StackValue(v));
        END_OP(MoreIter);
      }

      case JSOp::IsNoIter: {
        // iter => iter, bool
        bool result = stack[0].asValue().isMagic(JS_NO_ITER_VALUE);
        PUSH(StackValue(BooleanValue(result)));
        END_OP(IsNoIter);
      }

      case JSOp::EndIter: {
        // iter, interval =>
        stack.pop();
        CloseIterator(&stack.pop().asValue().toObject());
        END_OP(EndIter);
      }

      case JSOp::CloseIter: {
        state.obj0 = &stack.pop().asValue().toObject();
        ADVANCE(JSOpLength_CloseIter);
        goto ic_CloseIter;
      }

      case JSOp::CheckIsObj: {
        if (!stack[0].asValue().isObject()) {
          PUSH_EXIT_FRAME();
          MOZ_ALWAYS_FALSE(js::ThrowCheckIsObject(
              cx, js::CheckIsObjectKind(GET_UINT8(pc.pc))));
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
        PUSH(StackValue(ObjectValue(*ret)));
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
        ADVANCE(JSOpLength_NewArray);
        goto ic_NewArray;
      }

      case JSOp::InitElemArray: {
        // array, val => array
        state.value0 = stack.pop().asValue();
        state.obj0 = &stack[0].asValue().toObject();
        {
          PUSH_EXIT_FRAME();
          InitElemArrayOperation(cx, pc.pc, state.obj0.as<ArrayObject>(),
                                 state.value0);
        }
        END_OP(InitElemArray);
      }

      case JSOp::Hole: {
        PUSH(StackValue(MagicValue(JS_ELEMENTS_HOLE)));
        END_OP(Hole);
      }

      case JSOp::RegExp: {
        JSObject* obj;
        {
          PUSH_EXIT_FRAME();
          state.obj0 = script->getRegExp(pc.pc);
          obj = CloneRegExpObject(cx, state.obj0.as<RegExpObject>());
          if (!obj) {
            goto error;
          }
        }
        PUSH(StackValue(ObjectValue(*obj)));
        END_OP(RegExp);
      }

      case JSOp::Lambda: {
        state.fun0 = script->getFunction(pc.pc);
        state.obj0 = frame->environmentChain();
        JSObject* res;
        {
          PUSH_EXIT_FRAME();
          res = js::Lambda(cx, state.fun0, state.obj0);
          if (!res) {
            goto error;
          }
        }
        PUSH(StackValue(ObjectValue(*res)));
        END_OP(Lambda);
      }

      case JSOp::SetFunName: {
        // fun, name => fun
        state.value0 = stack.pop().asValue();  // name
        state.fun0 = &stack[0].asValue().toObject().as<JSFunction>();
        FunctionPrefixKind prefixKind = FunctionPrefixKind(GET_UINT8(pc.pc));
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
        state.fun0 = script->getFunction(pc.pc);
        JSObject* obj;
        {
          PUSH_EXIT_FRAME();
          obj = FunWithProtoOperation(cx, state.fun0, state.obj1, state.obj0);
          if (!obj) {
            goto error;
          }
        }
        PUSH(StackValue(ObjectValue(*obj)));
        END_OP(FunWithProto);
      }

      case JSOp::BuiltinObject: {
        auto kind = BuiltinObjectKind(GET_UINT8(pc.pc));
        JSObject* builtin;
        {
          PUSH_EXIT_FRAME();
          builtin = BuiltinObjectOperation(cx, kind);
          if (!builtin) {
            goto error;
          }
        }
        PUSH(StackValue(ObjectValue(*builtin)));
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
        state.argc = GET_ARGC(pc.pc);
        state.extraArgs = 2;
        state.spreadCall = false;
        ADVANCE(JSOpLength_Call);
        goto ic_Call;
      }

      case JSOp::SuperCall:
      case JSOp::New:
      case JSOp::NewContent: {
        static_assert(JSOpLength_SuperCall == JSOpLength_New);
        static_assert(JSOpLength_SuperCall == JSOpLength_NewContent);
        state.argc = GET_ARGC(pc.pc);
        state.extraArgs = 3;
        state.spreadCall = false;
        ADVANCE(JSOpLength_SuperCall);
        goto ic_Call;
      }

      case JSOp::SpreadCall:
      case JSOp::SpreadEval:
      case JSOp::StrictSpreadEval: {
        static_assert(JSOpLength_SpreadCall == JSOpLength_SpreadEval);
        static_assert(JSOpLength_SpreadCall == JSOpLength_StrictSpreadEval);
        state.argc = 1;
        state.extraArgs = 2;
        state.spreadCall = true;
        ADVANCE(JSOpLength_SpreadCall);
        goto ic_Call;
      }

      case JSOp::SpreadSuperCall:
      case JSOp::SpreadNew: {
        static_assert(JSOpLength_SpreadSuperCall == JSOpLength_SpreadNew);
        state.argc = 1;
        state.extraArgs = 3;
        state.spreadCall = true;
        ADVANCE(JSOpLength_SpreadSuperCall);
        goto ic_Call;
      }

      case JSOp::OptimizeSpreadCall: {
        state.value0 = stack.pop().asValue();
        ADVANCE(JSOpLength_OptimizeSpreadCall);
        goto ic_OptimizeSpreadCall;
      }

      case JSOp::ImplicitThis: {
        state.obj0 = frame->environmentChain();
        state.name0 = script->getName(pc.pc);
        {
          PUSH_EXIT_FRAME();
          if (!ImplicitThisOperation(cx, state.obj0, state.name0, &state.res)) {
            goto error;
          }
        }
        PUSH(StackValue(state.res));
        END_OP(ImplicitThis);
      }

      case JSOp::CallSiteObj: {
        JSObject* cso = script->getObject(pc.pc);
        MOZ_ASSERT(!cso->as<ArrayObject>().isExtensible());
        MOZ_ASSERT(cso->as<ArrayObject>().containsPure(
            frameMgr.cxForLocalUseOnly()->names().raw));
        PUSH(StackValue(ObjectValue(*cso)));
        END_OP(CallSiteObj);
      }

      case JSOp::IsConstructing: {
        PUSH(StackValue(MagicValue(JS_IS_CONSTRUCTING)));
        END_OP(IsConstructing);
      }

      case JSOp::SuperFun: {
        JSObject* superEnvFunc = &stack.pop().asValue().toObject();
        JSObject* superFun = SuperFunOperation(superEnvFunc);
        PUSH(StackValue(ObjectOrNullValue(superFun)));
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
        PUSH(StackValue(ObjectValue(*generator)));
        END_OP(Generator);
      }

      case JSOp::InitialYield: {
        // gen => rval, gen, resumeKind
        state.obj0 = &stack[0].asValue().toObject();
        uint32_t frameSize = stack.frameSize(frame);
        {
          PUSH_EXIT_FRAME();
          if (!NormalSuspend(cx, state.obj0, frame, frameSize, pc.pc)) {
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
          if (!NormalSuspend(cx, state.obj0, frame, frameSize, pc.pc)) {
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
          if (!FinalSuspend(cx, state.obj0, pc.pc)) {
            goto error;
          }
        }
        stack.popFrame(frameMgr.cxForLocalUseOnly());
        stack.pop();  // fake return address
        return true;
      }

      case JSOp::IsGenClosing: {
        PUSH(StackValue(MagicValue(JS_GENERATOR_CLOSING)));
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
        PUSH(StackValue(ObjectValue(*promise)));
        END_OP(AsyncAwait);
      }

      case JSOp::AsyncResolve: {
        // valueOrReason, gen => promise
        state.obj0 = &stack.pop().asValue().toObject();  // gen
        state.value0 = stack.pop().asValue();            // valueOrReason
        auto resolveKind = AsyncFunctionResolveKind(GET_UINT8(pc.pc));
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
        PUSH(StackValue(ObjectValue(*promise)));
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
        PUSH(StackValue(BooleanValue(result)));
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
        PUSH(StackValue(state.value0));
        PUSH(StackValue(state.value1));
        END_OP(MaybeExtractAwaitValue);
      }

      case JSOp::ResumeKind: {
        GeneratorResumeKind resumeKind = ResumeKindFromPC(pc.pc);
        PUSH(StackValue(Int32Value(int32_t(resumeKind))));
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
        int32_t icIndex = GET_INT32(pc.pc);
        frame->interpreterICEntry() = frame->icScript()->icEntries() + icIndex;
        END_OP(JumpTarget);
      }
      case JSOp::LoopHead: {
        int32_t icIndex = GET_INT32(pc.pc);
        frame->interpreterICEntry() = frame->icScript()->icEntries() + icIndex;
        END_OP(LoopHead);
      }
      case JSOp::AfterYield: {
        int32_t icIndex = GET_INT32(pc.pc);
        frame->interpreterICEntry() = frame->icScript()->icEntries() + icIndex;
        END_OP(AfterYield);
      }

      case JSOp::Goto: {
        ADVANCE(GET_JUMP_OFFSET(pc.pc));
        break;
      }

      case JSOp::Coalesce: {
        if (!stack[0].asValue().isNullOrUndefined()) {
          ADVANCE(GET_JUMP_OFFSET(pc.pc));
          break;
        } else {
          END_OP(Coalesce);
        }
      }

      case JSOp::Case: {
        bool cond = stack.pop().asValue().toBoolean();
        if (cond) {
          stack.pop();
          ADVANCE(GET_JUMP_OFFSET(pc.pc));
          break;
        } else {
          END_OP(Case);
        }
      }

      case JSOp::Default: {
        stack.pop();
        ADVANCE(GET_JUMP_OFFSET(pc.pc));
        break;
      }

      case JSOp::TableSwitch: {
        int32_t len = GET_JUMP_OFFSET(pc.pc);
        int32_t low = GET_JUMP_OFFSET(pc.pc + 1 * JUMP_OFFSET_LEN);
        int32_t high = GET_JUMP_OFFSET(pc.pc + 2 * JUMP_OFFSET_LEN);
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
          len = script->tableSwitchCaseOffset(pc.pc, uint32_t(i)) -
                script->pcToOffset(pc.pc);
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
        PUSH(StackValue(*ret));
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
          PUSH(StackValue(*ret));
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
          PUSH(StackValue(thisval));
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
          MOZ_ALWAYS_FALSE(ThrowMsgOperation(cx, GET_UINT8(pc.pc)));
          goto error;
        }
        END_OP(ThrowMsg);
      }

      case JSOp::ThrowSetConst: {
        {
          PUSH_EXIT_FRAME();
          ReportRuntimeLexicalError(cx, JSMSG_BAD_CONST_ASSIGN, script, pc.pc);
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
        PUSH(StackValue(state.res));
        END_OP(Exception);
      }

      case JSOp::Finally: {
        END_OP(Finally);
      }

      case JSOp::Uninitialized: {
        PUSH(StackValue(MagicValue(JS_UNINITIALIZED_LEXICAL)));
        END_OP(Uninitialized);
      }
      case JSOp::InitLexical: {
        uint32_t i = GET_LOCALNO(pc.pc);
        frame->unaliasedLocal(i) = stack[0].asValue();
        END_OP(InitLexical);
      }

      case JSOp::InitAliasedLexical: {
        EnvironmentCoordinate ec = EnvironmentCoordinate(pc.pc);
        EnvironmentObject& obj = getEnvironmentFromCoordinate(frame, ec);
        obj.setAliasedBinding(ec, stack[0].asValue());
        END_OP(InitAliasedLexical);
      }
      case JSOp::CheckLexical: {
        if (stack[0].asValue().isMagic(JS_UNINITIALIZED_LEXICAL)) {
          PUSH_EXIT_FRAME();
          ReportRuntimeLexicalError(cx, JSMSG_UNINITIALIZED_LEXICAL, script,
                                    pc.pc);
          goto error;
        }
        END_OP(CheckLexical);
      }
      case JSOp::CheckAliasedLexical: {
        if (stack[0].asValue().isMagic(JS_UNINITIALIZED_LEXICAL)) {
          PUSH_EXIT_FRAME();
          ReportRuntimeLexicalError(cx, JSMSG_UNINITIALIZED_LEXICAL, script,
                                    pc.pc);
          goto error;
        }
        END_OP(CheckAliasedLexical);
      }

      case JSOp::BindGName: {
        state.obj0.set(
            &frameMgr.cxForLocalUseOnly()->global()->lexicalEnvironment());
        state.name0.set(script->getName(pc.pc));
        ADVANCE(JSOpLength_BindGName);
        goto ic_BindName;
      }
      case JSOp::BindName: {
        state.obj0.set(frame->environmentChain());
        ADVANCE(JSOpLength_BindName);
        goto ic_BindName;
      }
      case JSOp::GetGName: {
        state.obj0.set(
            &frameMgr.cxForLocalUseOnly()->global()->lexicalEnvironment());
        ADVANCE(JSOpLength_GetGName);
        goto ic_GetName;
      }
      case JSOp::GetName: {
        state.obj0.set(frame->environmentChain());
        ADVANCE(JSOpLength_GetName);
        goto ic_GetName;
      }

      case JSOp::GetArg: {
        unsigned i = GET_ARGNO(pc.pc);
        if (script->argsObjAliasesFormals()) {
          PUSH(StackValue(frame->argsObj().arg(i)));
        } else {
          PUSH(StackValue(frame->unaliasedFormal(i)));
        }
        END_OP(GetArg);
      }

      case JSOp::GetFrameArg: {
        uint32_t i = GET_ARGNO(pc.pc);
        PUSH(StackValue(frame->unaliasedFormal(i, DONT_CHECK_ALIASING)));
        END_OP(GetFrameArg);
      }

      case JSOp::GetLocal: {
        uint32_t i = GET_LOCALNO(pc.pc);
        PUSH(StackValue(frame->unaliasedLocal(i)));
        END_OP(GetLocal);
      }

      case JSOp::ArgumentsLength: {
        PUSH(StackValue(Int32Value(frame->numActualArgs())));
        END_OP(ArgumentsLength);
      }

      case JSOp::GetActualArg: {
        MOZ_ASSERT(!script->needsArgsObj());
        uint32_t index = stack[0].asValue().toInt32();
        stack[0] = StackValue(frame->unaliasedActual(index));
        END_OP(GetActualArg);
      }

      case JSOp::GetAliasedVar:
      case JSOp::GetAliasedDebugVar: {
        static_assert(JSOpLength_GetAliasedVar ==
                      JSOpLength_GetAliasedDebugVar);
        EnvironmentCoordinate ec = EnvironmentCoordinate(pc.pc);
        EnvironmentObject& obj = getEnvironmentFromCoordinate(frame, ec);
        PUSH(StackValue(obj.aliasedBinding(ec)));
        END_OP(GetAliasedVar);
      }

      case JSOp::GetImport: {
        state.obj0 = frame->environmentChain();
        state.value0 = stack[0].asValue();
        {
          PUSH_EXIT_FRAME();
          if (!GetImportOperation(cx, state.obj0, script, pc.pc,
                                  &state.value0)) {
            goto error;
          }
        }
        stack[0] = StackValue(state.value0);
        END_OP(GetImport);
      }

      case JSOp::GetIntrinsic: {
        ADVANCE(JSOpLength_GetIntrinsic);
        goto ic_GetIntrinsic;
      }

      case JSOp::Callee: {
        PUSH(StackValue(frame->calleev()));
        END_OP(Callee);
      }

      case JSOp::EnvCallee: {
        uint8_t numHops = GET_UINT8(pc.pc);
        JSObject* env = &frame->environmentChain()->as<EnvironmentObject>();
        for (unsigned i = 0; i < numHops; i++) {
          env = &env->as<EnvironmentObject>().enclosingEnvironment();
        }
        PUSH(StackValue(ObjectValue(env->as<CallObject>().callee())));
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
        state.value1 = stack.pop().asValue();
        state.value0 = stack.pop().asValue();
        PUSH(StackValue(state.value1));
        ADVANCE(JSOpLength_SetProp);
        goto ic_SetProp;
      }

      case JSOp::InitProp:
      case JSOp::InitHiddenProp:
      case JSOp::InitLockedProp: {
        static_assert(JSOpLength_InitProp == JSOpLength_InitHiddenProp);
        static_assert(JSOpLength_InitProp == JSOpLength_InitLockedProp);
        state.value1 = stack.pop().asValue();
        state.value0 = stack[0].asValue();
        ADVANCE(JSOpLength_InitProp);
        goto ic_SetProp;
      }
      case JSOp::InitGLexical: {
        state.value1 = stack[0].asValue();
        state.value0.setObject(
            frameMgr.cxForLocalUseOnly()->global()->lexicalEnvironment());
        ADVANCE(JSOpLength_InitGLexical);
        goto ic_SetProp;
      }

      case JSOp::SetArg: {
        unsigned i = GET_ARGNO(pc.pc);
        if (script->argsObjAliasesFormals()) {
          frame->argsObj().setArg(i, stack[0].asValue());
        } else {
          frame->unaliasedFormal(i) = stack[0].asValue();
        }
        END_OP(SetArg);
      }

      case JSOp::SetLocal: {
        uint32_t i = GET_LOCALNO(pc.pc);
        frame->unaliasedLocal(i) = stack[0].asValue();
        END_OP(SetLocal);
      }

      case JSOp::SetAliasedVar: {
        EnvironmentCoordinate ec = EnvironmentCoordinate(pc.pc);
        EnvironmentObject& obj = getEnvironmentFromCoordinate(frame, ec);
        MOZ_ASSERT(!IsUninitializedLexical(obj.aliasedBinding(ec)));
        obj.setAliasedBinding(ec, stack[0].asValue());
        END_OP(SetAliasedVar);
      }

      case JSOp::SetIntrinsic: {
        state.value0 = stack[0].asValue();
        {
          PUSH_EXIT_FRAME();
          if (!SetIntrinsicOperation(cx, script, pc.pc, state.value0)) {
            goto error;
          }
        }
        END_OP(SetIntrinsic);
      }

      case JSOp::PushLexicalEnv: {
        state.scope0 = script->getScope(pc.pc);
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
        state.scope0 = script->getScope(pc.pc);
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
        state.scope0 = script->getScope(pc.pc);
        {
          PUSH_EXIT_FRAME();
          if (!frame->pushVarEnvironment(cx, state.scope0)) {
            goto error;
          }
        }
        END_OP(PushVarEnv);
      }
      case JSOp::EnterWith: {
        state.scope0 = script->getScope(pc.pc);
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
        PUSH(StackValue(ObjectValue(*varObj)));
        END_OP(BindVar);
      }

      case JSOp::GlobalOrEvalDeclInstantiation: {
        GCThingIndex lastFun = GET_GCTHING_INDEX(pc.pc);
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
        state.name0 = script->getName(pc.pc);
        state.obj0 = frame->environmentChain();
        {
          PUSH_EXIT_FRAME();
          if (!DeleteNameOperation(cx, state.name0, state.obj0, &state.res)) {
            goto error;
          }
        }
        PUSH(StackValue(state.res));
        END_OP(DelName);
      }

      case JSOp::Arguments: {
        {
          PUSH_EXIT_FRAME();
          if (!NewArgumentsObject(cx, frame, &state.res)) {
            goto error;
          }
        }
        PUSH(StackValue(state.res));
        END_OP(Arguments);
      }

      case JSOp::Rest: {
        ADVANCE(JSOpLength_Rest);
        goto ic_Rest;
      }

      case JSOp::FunctionThis: {
        {
          PUSH_EXIT_FRAME();
          if (!js::GetFunctionThis(cx, frame, &state.res)) {
            goto error;
          }
        }
        PUSH(StackValue(state.res));
        END_OP(FunctionThis);
      }

      case JSOp::Pop: {
        stack.pop();
        END_OP(Pop);
      }
      case JSOp::PopN: {
        uint32_t n = GET_UINT16(pc.pc);
        stack.popn(n);
        END_OP(PopN);
      }
      case JSOp::Dup: {
        StackValue value = stack[0];
        PUSH(value);
        END_OP(Dup);
      }
      case JSOp::Dup2: {
        StackValue value1 = stack[0];
        StackValue value2 = stack[1];
        PUSH(value2);
        PUSH(value1);
        END_OP(Dup2);
      }
      case JSOp::DupAt: {
        unsigned i = GET_UINT24(pc.pc);
        StackValue value = stack[i];
        PUSH(value);
        END_OP(DupAt);
      }
      case JSOp::Swap: {
        std::swap(stack[0], stack[1]);
        END_OP(Swap);
      }
      case JSOp::Pick: {
        unsigned i = GET_UINT8(pc.pc);
        StackValue tmp = stack[i];
        memmove(&stack[1], &stack[0], sizeof(StackValue) * i);
        stack[0] = tmp;
        END_OP(Pick);
      }
      case JSOp::Unpick: {
        unsigned i = GET_UINT8(pc.pc);
        StackValue tmp = stack[0];
        memmove(&stack[0], &stack[1], sizeof(StackValue) * i);
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

#define ICLOOP(fallback_body)                                             \
  for (state.stub = frame->interpreterICEntry()->firstStub(); state.stub; \
       state.stub = state.stub->maybeNext()) {                            \
    if (stub->isFallback()) {                                             \
      ICFallbackStub* fallback = stub->toFallbackStub();                  \
      fallback_body;                                                      \
      break;                                                              \
    } else {                                                              \
      ICCacheIRStub* cacheir = stub->toCacheIRStub();                     \
      (void)cacheir;                                                      \
      printf("trying to run cacheir stub: %p\n", cacheir);                \
      /* nothing */                                                       \
    }                                                                     \
  }

ic_launch_stub:
  do {
    if (!state.stub) {
      goto ic_fail;
    }
    if (state.stub->isFallback()) {
      goto* state.fallbackIC;
    }
    ICCacheIRStub* cstub = state.stub->toCacheIRStub();
    cstub->incrementEnteredCount();
    state.cacheIRReader.emplace(cstub->stubInfo());
  } while (0);

  while (true) {
    switch (state.cacheIRReader->readOp()) {
      case CacheOp::ReturnFromIC:
        goto* state.stubTail;
      default:
        goto ic_fail;
    }
  }

ic_fail:
  state.stub = state.stub->maybeNext();
  goto ic_launch_stub;

#define IC_KIND(kind, fallback_body, tail_body)              \
  ic_##kind : do {                                           \
    state.stub = frame->interpreterICEntry()->firstStub();   \
    state.fallbackIC = &&ic_##kind##_fallback;               \
    state.stubTail = &&ic_##kind##_tail;                     \
    goto ic_launch_stub;                                     \
  }                                                          \
  while (0)                                                  \
    ;                                                        \
  ic_##kind##_fallback : do {                                \
    ICFallbackStub* fallback = state.stub->toFallbackStub(); \
    fallback_body;                                           \
  }                                                          \
  while (0)                                                  \
    ;                                                        \
  ic_##kind##_tail : do {                                    \
    tail_body;                                               \
    NEXT_IC();                                               \
    goto dispatch;                                           \
  }                                                          \
  while (0)

  IC_KIND(
      GetName,
      {
        PUSH_EXIT_FRAME();
        if (!DoGetNameFallback(cx, frame, fallback, state.obj0, &state.res)) {
          goto error;
        }
      },
      { PUSH(StackValue(state.res)); });

  IC_KIND(
      Call,
      {
        uint32_t totalArgs =
            state.argc +
            state.extraArgs;  // this, callee, (cosntructing?), func args
        Value* args = reinterpret_cast<Value*>(&stack[0]);
        // Reverse values on the stack.
        for (uint32_t i = 0; i < totalArgs / 2; i++) {
          std::swap(args[i], args[totalArgs - 1 - i]);
        }
        {
          PUSH_EXIT_FRAME();
          if (state.spreadCall) {
            if (!DoSpreadCallFallback(cx, frame, fallback, args, &state.res)) {
              goto error;
            }
          } else {
            if (!DoCallFallback(cx, frame, fallback, state.argc, args,
                                &state.res)) {
              goto error;
            }
          }
        }
        stack.popn(totalArgs);
        PUSH(StackValue(state.res));
      },
      {});

  IC_KIND(
      Typeof,
      {
        PUSH_EXIT_FRAME();
        if (!DoTypeOfFallback(cx, frame, fallback, state.value0, &state.res)) {
          goto error;
        }
      },
      { PUSH(StackValue(state.res)); });

  IC_KIND(
      UnaryArith,
      {
        PUSH_EXIT_FRAME();
        if (!DoUnaryArithFallback(cx, frame, fallback, state.value0,
                                  &state.res)) {
          goto error;
        }
      },
      { PUSH(StackValue(state.res)); });

  IC_KIND(
      BinaryArith,
      {
        PUSH_EXIT_FRAME();
        if (!DoBinaryArithFallback(cx, frame, fallback, state.value0,
                                   state.value1, &state.res)) {
          goto error;
        }
      },
      { PUSH(StackValue(state.res)); });

  IC_KIND(
      ToBool,
      {
        PUSH_EXIT_FRAME();
        if (!DoToBoolFallback(cx, frame, fallback, state.value0, &state.res)) {
          goto error;
        }
      },
      {
        switch (state.op) {
          case JSOp::Not:
            PUSH(StackValue(BooleanValue(!state.res.toBoolean())));
            break;
          case JSOp::Or:
          case JSOp::JumpIfTrue: {
            bool result = state.res.toBoolean();
            if (result) {
              ADVANCE(state.jumpOffset);
            }
            break;
          }
          case JSOp::And:
          case JSOp::JumpIfFalse: {
            bool result = state.res.toBoolean();
            if (!result) {
              ADVANCE(state.jumpOffset);
            }
            break;
          }
          default:
            MOZ_CRASH("unexpected opcode");
        }
      });

  IC_KIND(
      Compare,
      {
        PUSH_EXIT_FRAME();
        if (!DoCompareFallback(cx, frame, fallback, state.value0, state.value1,
                               &state.res)) {
          goto error;
        }
      },
      { PUSH(StackValue(state.res)); });

  IC_KIND(
      InstanceOf,
      {
        PUSH_EXIT_FRAME();
        if (!DoInstanceOfFallback(cx, frame, fallback, state.value0,
                                  state.value1, &state.res)) {
          goto error;
        }
      },
      { PUSH(StackValue(state.res)); });

  IC_KIND(
      In,
      {
        PUSH_EXIT_FRAME();
        if (!DoInFallback(cx, frame, fallback, state.value0, state.value1,
                          &state.res)) {
          goto error;
        }
      },
      { PUSH(StackValue(state.res)); });

  IC_KIND(
      BindName,
      {
        PUSH_EXIT_FRAME();
        if (!DoBindNameFallback(cx, frame, fallback, state.obj0, &state.res)) {
          goto error;
        }
      },
      { PUSH(StackValue(state.res)); });

  IC_KIND(SetProp,
          {
            PUSH_EXIT_FRAME();
            if (!DoSetPropFallback(cx, frame, fallback, nullptr, state.value0,
                                   state.value1)) {
              goto error;
            }
          },
          {});

  IC_KIND(
      NewObject,
      {
        PUSH_EXIT_FRAME();
        if (!DoNewObjectFallback(cx, frame, fallback, &state.res)) {
          goto error;
        }
      },
      { PUSH(StackValue(state.res)); });

  IC_KIND(
      GetProp,
      {
        PUSH_EXIT_FRAME();
        if (!DoGetPropFallback(cx, frame, fallback, &state.value0,
                               &state.res)) {
          goto error;
        }
      },
      { PUSH(StackValue(state.res)); });

  IC_KIND(
      GetPropSuper,
      {
        PUSH_EXIT_FRAME();
        if (!DoGetPropSuperFallback(cx, frame, fallback, state.value0,
                                    &state.value1, &state.res)) {
          goto error;
        }
      },
      { PUSH(StackValue(state.res)); });

  IC_KIND(
      GetElem,
      {
        PUSH_EXIT_FRAME();
        if (!DoGetElemFallback(cx, frame, fallback, state.value0, state.value1,
                               &state.res)) {
          goto error;
        }
      },
      { PUSH(StackValue(state.res)); });

  IC_KIND(
      GetElemSuper,
      {
        PUSH_EXIT_FRAME();
        if (!DoGetElemSuperFallback(cx, frame, fallback, state.value0,
                                    state.value1, state.value2, &state.res)) {
          goto error;
        }
      },
      { PUSH(StackValue(state.res)); });

  IC_KIND(
      NewArray,
      {
        PUSH_EXIT_FRAME();
        if (!DoNewArrayFallback(cx, frame, fallback, &state.res)) {
          goto error;
        }
      },
      { PUSH(StackValue(state.res)); });

  IC_KIND(
      GetIntrinsic,
      {
        PUSH_EXIT_FRAME();
        if (!DoGetIntrinsicFallback(cx, frame, fallback, &state.res)) {
          goto error;
        }
      },
      { PUSH(StackValue(state.res)); });

  IC_KIND(SetElem,
          {
            PUSH_EXIT_FRAME();
            if (!DoSetElemFallback(cx, frame, fallback, nullptr, state.value0,
                                   state.value1, state.value2)) {
              goto error;
            }
          },
          {});

  IC_KIND(
      HasOwn,
      {
        PUSH_EXIT_FRAME();
        if (!DoHasOwnFallback(cx, frame, fallback, state.value0, state.value1,
                              &state.res)) {
          goto error;
        }
      },
      { PUSH(StackValue(state.res)); });

  IC_KIND(
      CheckPrivateField,
      {
        PUSH_EXIT_FRAME();
        if (!DoCheckPrivateFieldFallback(cx, frame, fallback, state.value0,
                                         state.value1, &state.res)) {
          goto error;
        }
      },
      { PUSH(StackValue(state.res)); });

  IC_KIND(
      GetIterator,
      {
        PUSH_EXIT_FRAME();
        if (!DoGetIteratorFallback(cx, frame, fallback, state.value0,
                                   &state.res)) {
          goto error;
        }
      },
      { PUSH(StackValue(state.res)); });

  IC_KIND(
      ToPropertyKey,
      {
        PUSH_EXIT_FRAME();
        if (!DoToPropertyKeyFallback(cx, frame, fallback, state.value0,
                                     &state.res)) {
          goto error;
        }
      },
      { PUSH(StackValue(state.res)); });

  IC_KIND(
      OptimizeSpreadCall,
      {
        PUSH_EXIT_FRAME();
        if (!DoOptimizeSpreadCallFallback(cx, frame, fallback, state.value0,
                                          &state.res)) {
          goto error;
        }
      },
      { PUSH(StackValue(state.res)); });

  IC_KIND(
      Rest,
      {
        PUSH_EXIT_FRAME();
        if (!DoRestFallback(cx, frame, fallback, &state.res)) {
          goto error;
        }
      },
      { PUSH(StackValue(state.res)); });

  IC_KIND(CloseIter,
          {
            PUSH_EXIT_FRAME();
            if (!DoCloseIterFallback(cx, frame, fallback, state.obj0)) {
              goto error;
            }
          },
          {});

error:
#ifdef TRACE_INTERP
  printf("HandleException\n");
#endif
  do {
    ResumeFromException rfe;
    {
      PUSH_EXIT_FRAME();
      HandleException(&rfe);
    }

    switch (rfe.kind) {
      case ExceptionResumeKind::EntryFrame:
#ifdef TRACE_INTERP
        printf(" -> Return from entry frame\n");
#endif
        *ret = MagicValue(JS_ION_ERROR);
        stack.popFrame(frameMgr.cxForLocalUseOnly());
        stack.pop();  // fake return address
        return false;
      case ExceptionResumeKind::Catch:
        pc.pc = frame->interpreterPC();
#ifdef TRACE_INTERP
        printf(" -> catch to pc %p\n", pc.pc);
#endif
        goto dispatch;
      case ExceptionResumeKind::Finally:
        pc.pc = frame->interpreterPC();
#ifdef TRACE_INTERP
        printf(" -> finally to pc %p\n", pc.pc);
#endif
        PUSH(StackValue(rfe.exception));
        PUSH(StackValue(BooleanValue(true)));
        goto dispatch;
      case ExceptionResumeKind::ForcedReturnBaseline:
#ifdef TRACE_INTERP
        printf(" -> forced return\n");
#endif
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
            "Unexpected WasmCatch exception-resume kind in Portable Baseline");
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
    PUSH(StackValue(argv[argc - 1 - i]));
  }
  PUSH(StackValue(calleeToken));
  PUSH(StackValue(
      MakeFrameDescriptorForJitCall(FrameType::CppToJSJit, numActualArgs)));
  PUSH(StackValue(nullptr));  // Fake return address.

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
