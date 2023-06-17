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

#include "jsapi.h"

#include "jit/BaselineFrame.h"
#include "jit/BaselineIC.h"
#include "jit/BaselineJIT.h"
#include "jit/JitFrames.h"
#include "jit/JitScript.h"
#include "jit/JSJitFrameIter.h"
#include "jit/VMFunctions.h"
#include "vm/AsyncIteration.h"
#include "vm/EnvironmentObject.h"
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

  StackValue* allocate(size_t size) {
    if (reinterpret_cast<uintptr_t>(base) + size >
        reinterpret_cast<uintptr_t>(*sp)) {
      return nullptr;
    }
    (*sp) =
        reinterpret_cast<StackValue*>(reinterpret_cast<uintptr_t>(*sp) - size);
    return *sp;
  }

  bool push(StackValue v) {
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

  StackValue* cur() { return *sp; }
  void restore(StackValue* s) { *sp = s; }

  BaselineFrame* pushFrame(JSContext* cx, JSObject* envChain) {
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

  StackValue* pushExitFrame(BaselineFrame* prevFrame) {
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
    if (!push(StackValue(uint64_t(ExitFrameType::CallNative)))) {
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

static bool PortableBaselineInterpret(JSContext* cx_, Stack& stack,
                                      JSObject* envChain, Value* ret) {
  State state(cx_);

  if (!stack.pushFrame(cx_, envChain)) {
    return false;
  }

  BaselineFrame* frame = stack.frameFromFP();
  RootedScript script(cx_, frame->script());
  PC pc(frame);

  uint32_t nslots = script->nslots();
  for (uint32_t i = 0; i < nslots; i++) {
    if (!stack.push(StackValue(UndefinedValue()))) {
      return false;
    }
  }
  ret->setUndefined();

  if (CalleeTokenIsFunction(frame->calleeToken())) {
    JSFunction* func = CalleeTokenToFunction(frame->calleeToken());
    frame->setEnvironmentChain(func->environment());
    if (func->needsFunctionEnvironmentObjects()) {
      if (!js::InitFunctionEnvironmentObjects(cx_, frame)) {
        return false;
      }
    }
  }

  VMFrameManager frameMgr(cx_, frame);

  while (true) {
  dispatch:
    frame->interpreterPC() = pc.pc;

#define NYI_OPCODE(op)                               \
  case JSOp::op:                                     \
    printf("not-yet-implemented opcode: " #op "\n"); \
    MOZ_CRASH("Bad opcode");                         \
    break;

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

#if 0
    printf("stack[0] = %" PRIx64 " stack[1] = %" PRIx64 " stack[2] = %" PRIx64
           "\n",
           stack[0].asUInt64(), stack[1].asUInt64(), stack[2].asUInt64());
    printf("script = %p pc = %p: %s (ic %d)\n", script.get(), pc.pc,
           CodeName(state.op),
           (int)(frame->interpreterICEntry() -
                 script->jitScript()->icScript()->icEntries()));
#endif

    switch (state.op) {
      case JSOp::Nop: {
        END_OP(Nop);
      }
      case JSOp::Undefined: {
        stack.push(StackValue(UndefinedValue()));
        END_OP(Undefined);
      }
      case JSOp::Null: {
        stack.push(StackValue(NullValue()));
        END_OP(Null);
      }
      case JSOp::False: {
        stack.push(StackValue(BooleanValue(false)));
        END_OP(False);
      }
      case JSOp::True: {
        stack.push(StackValue(BooleanValue(true)));
        END_OP(True);
      }
      case JSOp::Int32: {
        stack.push(StackValue(Int32Value(GET_INT32(pc.pc))));
        END_OP(Int32);
      }
      case JSOp::Zero: {
        stack.push(StackValue(Int32Value(0)));
        END_OP(Zero);
      }
      case JSOp::One: {
        stack.push(StackValue(Int32Value(1)));
        END_OP(One);
      }
      case JSOp::Int8: {
        stack.push(StackValue(Int32Value(GET_INT8(pc.pc))));
        END_OP(Int8);
      }
      case JSOp::Uint16: {
        stack.push(StackValue(Int32Value(GET_UINT16(pc.pc))));
        END_OP(Uint16);
      }
      case JSOp::Uint24: {
        stack.push(StackValue(Int32Value(GET_UINT24(pc.pc))));
        END_OP(Uint24);
      }
      case JSOp::Double: {
        stack.push(StackValue(GET_INLINE_VALUE(pc.pc)));
        END_OP(Double);
      }
      case JSOp::BigInt: {
        stack.push(StackValue(JS::BigIntValue(script->getBigInt(pc.pc))));
        END_OP(BigInt);
      }
      case JSOp::String: {
        stack.push(StackValue(StringValue(script->getString(pc.pc))));
        END_OP(String);
      }
      case JSOp::Symbol: {
        stack.push(StackValue(
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
            return false;
          }
        }
        stack.push(StackValue(StringValue(result)));
        END_OP(ToString);
      }

      case JSOp::IsNullOrUndefined: {
        bool result =
            stack[0].asValue().isNull() || stack[0].asValue().isUndefined();
        stack[0] = StackValue(BooleanValue(result));
        END_OP(IsNullOrUndefined);
      }

      case JSOp::GlobalThis: {
        stack.push(StackValue(ObjectValue(*frameMgr.cxForLocalUseOnly()
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
        stack.push(StackValue(state.value0));
        END_OP(NonSyntacticGlobalThis);
      }

      case JSOp::NewTarget: {
        stack.push(StackValue(frame->newTarget()));
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
            return false;
          }
        }
        stack.push(StackValue(ObjectValue(*promise)));
        END_OP(DynamicImport);
      }

      case JSOp::ImportMeta: {
        JSObject* metaObject;
        {
          PUSH_EXIT_FRAME();
          metaObject = ImportMetaOperation(cx, script);
          if (!metaObject) {
            return false;
          }
        }
        stack.push(StackValue(ObjectValue(*metaObject)));
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
        stack.push(StackValue(ObjectValue(*script->getObject(pc.pc))));
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
          stack.push(StackValue(Int32Value(state.value1.toInt32() + 1)));
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
            return false;
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
            return false;
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
            return false;
          }
        }
        stack.push(StackValue(BooleanValue(res)));
        END_OP(DelProp);
      }
      case JSOp::StrictDelProp: {
        state.value0 = stack.pop().asValue();
        state.name0 = script->getName(pc.pc);
        bool res = false;
        {
          PUSH_EXIT_FRAME();
          if (!DelPropOperation<true>(cx, state.value0, state.name0, &res)) {
            return false;
          }
        }
        stack.push(StackValue(BooleanValue(res)));
        END_OP(StrictDelProp);
      }
      case JSOp::DelElem: {
        state.value1 = stack.pop().asValue();
        state.value0 = stack.pop().asValue();
        bool res = false;
        {
          PUSH_EXIT_FRAME();
          if (!DelElemOperation<true>(cx, state.value0, state.value1, &res)) {
            return false;
          }
        }
        stack.push(StackValue(BooleanValue(res)));
        END_OP(DelElem);
      }
      case JSOp::StrictDelElem: {
        state.value1 = stack.pop().asValue();
        state.value0 = stack.pop().asValue();
        bool res = false;
        {
          PUSH_EXIT_FRAME();
          if (!DelElemOperation<true>(cx, state.value0, state.value1, &res)) {
            return false;
          }
        }
        stack.push(StackValue(BooleanValue(res)));
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
            return false;
          }
        }
        stack.push(StackValue(SymbolValue(symbol)));
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

        stack.push(StackValue(ObjectOrNullValue(superBase)));
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
            return false;
          }
        }
        stack.push(StackValue(state.value2));
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
            return false;
          }
        }
        stack.push(StackValue(state.value2));  // value
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
        stack.push(StackValue(v));
        END_OP(MoreIter);
      }

      case JSOp::IsNoIter: {
        // iter => iter, bool
        bool result = stack[0].asValue().isMagic(JS_NO_ITER_VALUE);
        stack.push(StackValue(BooleanValue(result)));
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
          return false;  // TODO: goto error
        }
        END_OP(CheckIsObj);
      }

      case JSOp::CheckObjCoercible: {
        state.value0 = stack[0].asValue();
        if (state.value0.isNullOrUndefined()) {
          PUSH_EXIT_FRAME();
          MOZ_ALWAYS_FALSE(ThrowObjectCoercible(cx, state.value0));
          return false;  // TOD: goto error
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
            return false;
          }
        }
        stack.push(StackValue(ObjectValue(*ret)));
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
            return false;
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
        stack.push(StackValue(MagicValue(JS_ELEMENTS_HOLE)));
        END_OP(Hole);
      }

      case JSOp::RegExp: {
        JSObject* obj;
        {
          PUSH_EXIT_FRAME();
          state.obj0 = script->getRegExp(pc.pc);
          obj = CloneRegExpObject(cx, state.obj0.as<RegExpObject>());
          if (!obj) {
            return false;
          }
        }
        stack.push(StackValue(ObjectValue(*obj)));
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
            return false;
          }
        }
        stack.push(StackValue(ObjectValue(*res)));
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
            return false;
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
            return false;
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
            return false;
          }
        }
        stack.push(StackValue(ObjectValue(*obj)));
        END_OP(FunWithProto);
      }

      case JSOp::BuiltinObject: {
        auto kind = BuiltinObjectKind(GET_UINT8(pc.pc));
        JSObject* builtin;
        {
          PUSH_EXIT_FRAME();
          builtin = BuiltinObjectOperation(cx, kind);
          if (!builtin) {
            return false;
          }
        }
        stack.push(StackValue(ObjectValue(*builtin)));
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
            return false;
          }
        }
        stack.push(StackValue(state.res));
        END_OP(ImplicitThis);
      }

      case JSOp::CallSiteObj: {
        JSObject* cso = script->getObject(pc.pc);
        MOZ_ASSERT(!cso->as<ArrayObject>().isExtensible());
        MOZ_ASSERT(cso->as<ArrayObject>().containsPure(
            frameMgr.cxForLocalUseOnly()->names().raw));
        stack.push(StackValue(ObjectValue(*cso)));
        END_OP(CallSiteObj);
      }

      case JSOp::IsConstructing: {
        stack.push(StackValue(MagicValue(JS_IS_CONSTRUCTING)));
        END_OP(IsConstructing);
      }

      case JSOp::SuperFun: {
        JSObject* superEnvFunc = &stack.pop().asValue().toObject();
        JSObject* superFun = SuperFunOperation(superEnvFunc);
        stack.push(StackValue(ObjectOrNullValue(superFun)));
        END_OP(SuperFun);
      }

      case JSOp::CheckThis:
      case JSOp::CheckThisReinit: {
        static_assert(JSOpLength_CheckThis == JSOpLength_CheckThisReinit);
        if (!stack[0].asValue().isMagic(JS_UNINITIALIZED_LEXICAL)) {
          PUSH_EXIT_FRAME();
          MOZ_ALWAYS_FALSE(ThrowInitializedThis(cx));
          return false;
        }
        END_OP(CheckThis);
      }

      case JSOp::Generator: {
        JSObject* generator;
        {
          PUSH_EXIT_FRAME();
          generator = CreateGeneratorFromFrame(cx, frame);
          if (!generator) {
            return false;
          }
        }
        stack.push(StackValue(ObjectValue(*generator)));
        END_OP(Generator);
      }

      case JSOp::InitialYield: {
        *ret = stack.pop().asValue();
        state.obj0 = &ret->toObject();
        {
          PUSH_EXIT_FRAME();
          MOZ_CRASH("todo: call jit::NormalSuspend");
        }
        stack.popFrame(frameMgr.cxForLocalUseOnly());
        stack.pop();  // fake return address
        return true;
      }

      case JSOp::FinalYieldRval: {
        state.obj0 = &stack.pop().asValue().toObject();
        {
          PUSH_EXIT_FRAME();
          MOZ_CRASH("todo: call jit::NormalSuspend");
        }
        stack.popFrame(frameMgr.cxForLocalUseOnly());
        stack.pop();  // fake return address
        return true;
      }

      case JSOp::Yield: {
        state.obj0 = &stack.pop().asValue().toObject();
        {
          PUSH_EXIT_FRAME();
          MOZ_CRASH("todo: call jit::NormalSuspend");
        }
        stack.popFrame(frameMgr.cxForLocalUseOnly());
        stack.pop();  // fake return address
        return true;
      }

      case JSOp::IsGenClosing: {
        stack.push(StackValue(MagicValue(JS_GENERATOR_CLOSING)));
        END_OP(IsGenClosing);
      }

        NYI_OPCODE(AsyncAwait);
        NYI_OPCODE(AsyncResolve);
        NYI_OPCODE(Await);

      case JSOp::CanSkipAwait: {
        // value => value, can_skip
        state.value0 = stack[0].asValue();
        bool result = false;
        {
          PUSH_EXIT_FRAME();
          if (!CanSkipAwait(cx, state.value0, &result)) {
            return false;
          }
        }
        stack.push(StackValue(BooleanValue(result)));
        END_OP(CanSkipAwait);
      }

        NYI_OPCODE(MaybeExtractAwaitValue);

      case JSOp::ResumeKind: {
        GeneratorResumeKind resumeKind = ResumeKindFromPC(pc.pc);
        stack.push(StackValue(Int32Value(int32_t(resumeKind))));
        END_OP(ResumeKind);
      }

        NYI_OPCODE(CheckResumeKind);
        NYI_OPCODE(Resume);

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

        NYI_OPCODE(TableSwitch);

      case JSOp::Return: {
        *ret = stack.pop().asValue();
        stack.popFrame(frameMgr.cxForLocalUseOnly());
        stack.pop();  // fake return address
        return true;
      }

      case JSOp::GetRval: {
        stack.push(StackValue(*ret));
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

        NYI_OPCODE(CheckReturn);
        NYI_OPCODE(Throw);
        NYI_OPCODE(ThrowMsg);
        NYI_OPCODE(ThrowSetConst);

      case JSOp::Try:
      case JSOp::TryDestructuring: {
        static_assert(JSOpLength_Try == JSOpLength_TryDestructuring);
        END_OP(Try);
      }

      case JSOp::Exception: {
        {
          PUSH_EXIT_FRAME();
          if (!GetAndClearException(cx, &state.res)) {
            return false;
          }
        }
        stack.push(StackValue(state.res));
        END_OP(Exception);
      }

      case JSOp::Finally: {
        END_OP(Finally);
      }

      case JSOp::Uninitialized: {
        stack.push(StackValue(MagicValue(JS_UNINITIALIZED_LEXICAL)));
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
          return false;
        }
        END_OP(CheckLexical);
      }
      case JSOp::CheckAliasedLexical: {
        if (stack[0].asValue().isMagic(JS_UNINITIALIZED_LEXICAL)) {
          PUSH_EXIT_FRAME();
          ReportRuntimeLexicalError(cx, JSMSG_UNINITIALIZED_LEXICAL, script,
                                    pc.pc);
          return false;
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
          stack.push(StackValue(frame->argsObj().arg(i)));
        } else {
          stack.push(StackValue(frame->unaliasedFormal(i)));
        }
        END_OP(GetArg);
      }

      case JSOp::GetFrameArg: {
        uint32_t i = GET_ARGNO(pc.pc);
        stack.push(StackValue(frame->unaliasedFormal(i, DONT_CHECK_ALIASING)));
        END_OP(GetFrameArg);
      }

      case JSOp::GetLocal: {
        uint32_t i = GET_LOCALNO(pc.pc);
        stack.push(StackValue(frame->unaliasedLocal(i)));
        END_OP(GetLocal);
      }

      case JSOp::ArgumentsLength: {
        stack.push(StackValue(Int32Value(frame->numActualArgs())));
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
        stack.push(StackValue(obj.aliasedBinding(ec)));
        END_OP(GetAliasedVar);
      }

      case JSOp::GetImport: {
        state.obj0 = frame->environmentChain();
        state.value0 = stack[0].asValue();
        {
          PUSH_EXIT_FRAME();
          if (!GetImportOperation(cx, state.obj0, script, pc.pc,
                                  &state.value0)) {
            return false;
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
        stack.push(StackValue(frame->calleev()));
        END_OP(Callee);
      }

      case JSOp::EnvCallee: {
        uint8_t numHops = GET_UINT8(pc.pc);
        JSObject* env = &frame->environmentChain()->as<EnvironmentObject>();
        for (unsigned i = 0; i < numHops; i++) {
          env = &env->as<EnvironmentObject>().enclosingEnvironment();
        }
        stack.push(StackValue(ObjectValue(env->as<CallObject>().callee())));
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
        stack.push(StackValue(state.value1));
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
            return false;
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
            return false;
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

        NYI_OPCODE(RecreateLexicalEnv);
      case JSOp::FreshenLexicalEnv: {
        {
          PUSH_EXIT_FRAME();
          if (!frame->freshenLexicalEnvironment(cx)) {
            return false;
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
            return false;
          }
        }
        END_OP(PushClassBodyEnv);
      }
      case JSOp::PushVarEnv: {
        state.scope0 = script->getScope(pc.pc);
        {
          PUSH_EXIT_FRAME();
          if (!frame->pushVarEnvironment(cx, state.scope0)) {
            return false;
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
            return false;
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
        stack.push(StackValue(ObjectValue(*varObj)));
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
            // TODO: exception case?
            return false;
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
            return false;
          }
        }
        stack.push(StackValue(state.res));
        END_OP(DelName);
      }

      case JSOp::Arguments: {
        {
          PUSH_EXIT_FRAME();
          if (!NewArgumentsObject(cx, frame, &state.res)) {
            return false;
          }
        }
        stack.push(StackValue(state.res));
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
            return false;
          }
        }
        stack.push(StackValue(state.res));
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
        stack.push(value);
        END_OP(Dup);
      }
      case JSOp::Dup2: {
        StackValue value1 = stack[0];
        StackValue value2 = stack[1];
        stack.push(value2);
        stack.push(value1);
        END_OP(Dup2);
      }
      case JSOp::DupAt: {
        unsigned i = GET_UINT24(pc.pc);
        StackValue value = stack[i];
        stack.push(value);
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

#define ICLOOP(fallback_body)                                         \
  for (ICStub* stub = frame->interpreterICEntry()->firstStub(); stub; \
       stub = stub->maybeNext()) {                                    \
    if (stub->isFallback()) {                                         \
      ICFallbackStub* fallback = stub->toFallbackStub();              \
      fallback_body;                                                  \
      break;                                                          \
    } else {                                                          \
      ICCacheIRStub* cacheir = stub->toCacheIRStub();                 \
      (void)cacheir;                                                  \
      /* nothing */                                                   \
    }                                                                 \
  }

ic_GetName:
  ICLOOP({
    PUSH_EXIT_FRAME();
    if (!DoGetNameFallback(cx, frame, fallback, state.obj0, &state.res)) {
      return false;
    }
  });
ic_GetName_tail:
  stack.push(StackValue(state.res));
  NEXT_IC();
  goto dispatch;

ic_Call:
  ICLOOP({
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
          return false;
        }
      } else {
        if (!DoCallFallback(cx, frame, fallback, state.argc, args,
                            &state.res)) {
          return false;
        }
      }
    }
    stack.popn(totalArgs);
    stack.push(StackValue(state.res));
  });
ic_Call_tail:
  NEXT_IC();
  goto dispatch;

ic_Typeof:
  ICLOOP({
    PUSH_EXIT_FRAME();
    if (!DoTypeOfFallback(cx, frame, fallback, state.value0, &state.res)) {
      return false;
    }
  });
ic_Typeof_tail:
  stack.push(StackValue(state.res));
  NEXT_IC();
  goto dispatch;

ic_UnaryArith:
  ICLOOP({
    PUSH_EXIT_FRAME();
    if (!DoUnaryArithFallback(cx, frame, fallback, state.value0, &state.res)) {
      return false;
    }
  });
ic_UnaryArith_tail:
  stack.push(StackValue(state.res));
  NEXT_IC();
  goto dispatch;

ic_BinaryArith:
  ICLOOP({
    PUSH_EXIT_FRAME();
    if (!DoBinaryArithFallback(cx, frame, fallback, state.value0, state.value1,
                               &state.res)) {
      return false;
    }
  });
ic_BinaryArith_tail:
  stack.push(StackValue(state.res));
  NEXT_IC();
  goto dispatch;

ic_ToBool:
  ICLOOP({
    PUSH_EXIT_FRAME();
    if (!DoToBoolFallback(cx, frame, fallback, state.value0, &state.res)) {
      return false;
    }
  });
ic_ToBool_tail:
  switch (state.op) {
    case JSOp::Not:
      stack.push(StackValue(BooleanValue(!state.res.toBoolean())));
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
  NEXT_IC();
  goto dispatch;

ic_Compare:
  ICLOOP({
    PUSH_EXIT_FRAME();
    if (!DoCompareFallback(cx, frame, fallback, state.value0, state.value1,
                           &state.res)) {
      return false;
    }
  });
ic_Compare_tail:
  stack.push(StackValue(state.res));
  NEXT_IC();
  goto dispatch;

ic_InstanceOf:
  ICLOOP({
    PUSH_EXIT_FRAME();
    if (!DoInstanceOfFallback(cx, frame, fallback, state.value0, state.value1,
                              &state.res)) {
      return false;
    }
  });
ic_InstanceOf_tail:
  stack.push(StackValue(state.res));
  NEXT_IC();
  goto dispatch;

ic_In:
  ICLOOP({
    PUSH_EXIT_FRAME();
    if (!DoInFallback(cx, frame, fallback, state.value0, state.value1,
                      &state.res)) {
      return false;
    }
  });
ic_In_tail:
  stack.push(StackValue(state.res));
  NEXT_IC();
  goto dispatch;

ic_BindName:
  ICLOOP({
    PUSH_EXIT_FRAME();
    if (!DoBindNameFallback(cx, frame, fallback, state.obj0, &state.res)) {
      return false;
    }
  });
ic_BindName_tail:
  stack.push(StackValue(state.res));
  NEXT_IC();
  goto dispatch;

ic_SetProp:
  ICLOOP({
    PUSH_EXIT_FRAME();
    if (!DoSetPropFallback(cx, frame, fallback, nullptr, state.value0,
                           state.value1)) {
      return false;
    }
  });
ic_SetProp_tail:
  NEXT_IC();
  goto dispatch;

ic_NewObject:
  ICLOOP({
    PUSH_EXIT_FRAME();
    if (!DoNewObjectFallback(cx, frame, fallback, &state.res)) {
      return false;
    }
  });
ic_NewObject_tail:
  stack.push(StackValue(state.res));
  NEXT_IC();
  goto dispatch;

ic_GetProp:
  ICLOOP({
    PUSH_EXIT_FRAME();
    if (!DoGetPropFallback(cx, frame, fallback, &state.value0, &state.res)) {
      return false;
    }
  });
ic_GetProp_tail:
  stack.push(StackValue(state.res));
  NEXT_IC();
  goto dispatch;

ic_GetPropSuper:
  ICLOOP({
    PUSH_EXIT_FRAME();
    if (!DoGetPropSuperFallback(cx, frame, fallback, state.value0,
                                &state.value1, &state.res)) {
      return false;
    }
  });
ic_GetPropSuper_tail:
  stack.push(StackValue(state.res));
  NEXT_IC();
  goto dispatch;

ic_GetElem:
  ICLOOP({
    PUSH_EXIT_FRAME();
    if (!DoGetElemFallback(cx, frame, fallback, state.value0, state.value1,
                           &state.res)) {
      return false;
    }
  });
ic_GetElem_tail:
  stack.push(StackValue(state.res));
  NEXT_IC();
  goto dispatch;

ic_GetElemSuper:
  ICLOOP({
    PUSH_EXIT_FRAME();
    if (!DoGetElemSuperFallback(cx, frame, fallback, state.value0, state.value1,
                                state.value2, &state.res)) {
      return false;
    }
  });
ic_GetElemSuper_tail:
  stack.push(StackValue(state.res));
  NEXT_IC();
  goto dispatch;

ic_NewArray:
  ICLOOP({
    PUSH_EXIT_FRAME();
    if (!DoNewArrayFallback(cx, frame, fallback, &state.res)) {
      return false;
    }
  });
ic_NewArray_tail:
  stack.push(StackValue(state.res));
  NEXT_IC();
  goto dispatch;

ic_GetIntrinsic:
  ICLOOP({
    PUSH_EXIT_FRAME();
    if (!DoGetIntrinsicFallback(cx, frame, fallback, &state.res)) {
      return false;
    }
  });
ic_GetIntrinsic_tail:
  stack.push(StackValue(state.res));
  NEXT_IC();
  goto dispatch;

ic_SetElem:
  ICLOOP({
    PUSH_EXIT_FRAME();
    if (!DoSetElemFallback(cx, frame, fallback, nullptr, state.value0,
                           state.value1, state.value2)) {
      return false;
    }
  });
ic_SetElem_tail:
  NEXT_IC();
  goto dispatch;

ic_HasOwn:
  ICLOOP({
    PUSH_EXIT_FRAME();
    if (!DoHasOwnFallback(cx, frame, fallback, state.value0, state.value1,
                          &state.res)) {
      return false;
    }
  });
ic_HasOwn_tail:
  stack.push(StackValue(state.res));
  NEXT_IC();
  goto dispatch;

ic_CheckPrivateField:
  ICLOOP({
    PUSH_EXIT_FRAME();
    if (!DoCheckPrivateFieldFallback(cx, frame, fallback, state.value0,
                                     state.value1, &state.res)) {
      return false;
    }
  });
ic_CheckPrivateField_tail:
  stack.push(StackValue(state.res));
  NEXT_IC();
  goto dispatch;

ic_GetIterator:
  ICLOOP({
    PUSH_EXIT_FRAME();
    if (!DoGetIteratorFallback(cx, frame, fallback, state.value0, &state.res)) {
      return false;
    }
  });
ic_GetIterator_tail:
  stack.push(StackValue(state.res));
  NEXT_IC();
  goto dispatch;

ic_ToPropertyKey:
  ICLOOP({
    PUSH_EXIT_FRAME();
    if (!DoToPropertyKeyFallback(cx, frame, fallback, state.value0,
                                 &state.res)) {
      return false;
    }
  });
ic_ToPropertyKey_tail:
  stack.push(StackValue(state.res));
  NEXT_IC();
  goto dispatch;

ic_OptimizeSpreadCall:
  ICLOOP({
    PUSH_EXIT_FRAME();
    if (!DoOptimizeSpreadCallFallback(cx, frame, fallback, state.value0,
                                      &state.res)) {
      return false;
    }
  });
ic_OptimizeSpreadCall_tail:
  stack.push(StackValue(state.res));
  NEXT_IC();
  goto dispatch;

ic_Rest:
  ICLOOP({
    PUSH_EXIT_FRAME();
    if (!DoRestFallback(cx, frame, fallback, &state.res)) {
      return false;
    }
  });
ic_Rest_tail:
  stack.push(StackValue(state.res));
  NEXT_IC();
  goto dispatch;

ic_CloseIter:
  ICLOOP({
    PUSH_EXIT_FRAME();
    if (!DoCloseIterFallback(cx, frame, fallback, state.obj0)) {
      return false;
    }
  });
ic_CloseIter_tail:
  NEXT_IC();
  goto dispatch;
}

bool js::PortableBaselineTrampoline(JSContext* cx, size_t argc, Value* argv,
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

  for (size_t i = 0; i < argc; i++) {
    stack.push(StackValue(argv[argc - 1 - i]));
  }
  stack.push(StackValue(calleeToken));
  stack.push(
      StackValue(MakeFrameDescriptorForJitCall(FrameType::CppToJSJit, argc)));
  stack.push(StackValue(nullptr));  // Fake return address.

  if (!PortableBaselineInterpret(cx, stack, envChain, result)) {
    return false;
  }

  // Pop the descriptor, calleeToken, and args. (Return address is
  // popped in callee.)
  stack.popn(2 + argc);

  return true;
}

bool js::CanEnterPortableBaselineInterpreter(JSContext* cx, RunState& state) {
  if (!JitOptions.portableBaselineInterpreter) {
    return false;
  }
  if (state.script()->hasJitScript()) {
    return true;
  }
  if (state.script()->hasForceInterpreterOp()) {
    return false;
  }
  if (state.script()->nslots() > BaselineMaxScriptSlots) {
    return false;
  }
  if (state.isInvoke()) {
    InvokeState& invoke = *state.asInvoke();
    if (TooManyActualArguments(invoke.args().length())) {
      return false;
    }
  }
  if (state.script()->getWarmUpCount() <=
      JitOptions.portableBaselineInterpreterWarmUpThreshold) {
    return false;
  }
  if (!cx->realm()->ensureJitRealmExists(cx)) {
    return false;
  }

  AutoKeepJitScripts keepJitScript(cx);
  if (!state.script()->ensureHasJitScript(cx, keepJitScript)) {
    return false;
  }
  state.script()->updateJitCodeRaw(cx->runtime());
  return true;
}
