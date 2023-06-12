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
#include "vm/EnvironmentObject.h"
#include "vm/JitActivation.h"
#include "vm/JSScript.h"
#include "vm/Opcodes.h"
#include "vm/PlainObject.h"

#include "jit/JitScript-inl.h"
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

  Stack(PortableBaselineStack& pbs)
      : sp(reinterpret_cast<StackValue**>(&pbs.top)),
        fp(nullptr),
        base(reinterpret_cast<StackValue*>(pbs.base)) {}

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
  StackValue pop() { return *(*sp)++; }
  void popn(size_t len) { (*sp) += len; }

  StackValue* cur() { return *sp; }
  void restore(StackValue* s) { *sp = s; }

  BaselineFrame* pushFrame(JSContext* cx, JSObject* envChain) {
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

    cx->activation()->asJit()->setJSExitFP(reinterpret_cast<uint8_t*>(fp));

    return frame;
  }

  void popFrame(JSContext* cx) {
    StackValue* newTOS = fp + 1;
    fp = reinterpret_cast<StackValue*>(fp->asVoidPtr());

    cx->activation()->asJit()->setJSExitFP(reinterpret_cast<uint8_t*>(fp));

    restore(newTOS);
  }

  BaselineFrame* frameFromFP() {
    return reinterpret_cast<BaselineFrame*>(reinterpret_cast<uintptr_t>(fp) -
                                            BaselineFrame::Size());
  }

  StackValue& operator[](size_t index) { return (*sp)[index]; }
};

// TODO:
// - update GC scanning to scan PortableBaselineStack.
// - create a BaselineFrame in PortableBaselineInterpret, and root
//   everything on that (JSScript, JitScript).
// - opcode dispatch based on current interpreter PC in BaselineFrame.
// - IC interpreter state (current stub and IC PC).

struct State {
  RootedValue value0;
  RootedValue value1;
  RootedValue value2;
  RootedValue res;
  RootedObject obj0;
  RootedObject obj1;
  RootedObject obj2;
  RootedScript script0;
  Rooted<PropertyName*> name0;
  JSOp op;
  int argc;
  uint32_t jumpOffset;

  State(JSContext* cx)
      : value0(cx),
        value1(cx),
        value2(cx),
        res(cx),
        obj0(cx),
        obj1(cx),
        obj2(cx),
        script0(cx),
        name0(cx) {}
};

struct PC {
  jsbytecode* pc;

  explicit PC(BaselineFrame* frame) : pc(frame->interpreterPC()) {}

  void advance(BaselineFrame* frame, intptr_t delta) {
    pc += delta;
    frame->interpreterPC() = pc;
  }
};

static bool PortableBaselineInterpret(JSContext* cx, Stack& stack,
                                      JSObject* envChain, Value* ret) {
  State state(cx);

  if (!stack.pushFrame(cx, envChain)) {
    return false;
  }

  BaselineFrame* frame = stack.frameFromFP();
  PC pc(frame);

  while (true) {
  dispatch:

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

    state.op = JSOp(*pc.pc);
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
        stack.push(
            StackValue(JS::BigIntValue(frame->script()->getBigInt(pc.pc))));
        END_OP(BigInt);
      }
      case JSOp::String: {
        stack.push(StackValue(StringValue(frame->script()->getString(pc.pc))));
        END_OP(String);
      }
      case JSOp::Symbol: {
        stack.push(StackValue(cx->wellKnownSymbols().get(GET_UINT8(pc.pc))));
        END_OP(Symbol);
      }
      case JSOp::Void: {
        stack[0] = StackValue(JS::UndefinedValue());
        END_OP(Symbol);
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

        NYI_OPCODE(ToPropertyKey);
        NYI_OPCODE(ToString);
        NYI_OPCODE(IsNullOrUndefined);

      case JSOp::GlobalThis: {
        stack.push(StackValue(
            ObjectValue(*cx->global()->lexicalEnvironment().thisObject())));
        END_OP(GlobalThis);
      }

      case JSOp::NonSyntacticGlobalThis: {
        state.obj0 = frame->environmentChain();
        js::GetNonSyntacticGlobalThis(cx, state.obj0, &state.value0);
        stack.push(StackValue(state.value0));
        END_OP(NonSyntacticGlobalThis);
      }

        NYI_OPCODE(NewTarget);
        NYI_OPCODE(DynamicImport);
        NYI_OPCODE(ImportMeta);
        NYI_OPCODE(NewInit);
        NYI_OPCODE(NewObject);

      case JSOp::Object: {
        stack.push(StackValue(ObjectValue(*frame->script()->getObject(pc.pc))));
        END_OP(Object);
      }
      case JSOp::ObjWithProto: {
        state.value0 = stack[0].asValue();
        JSObject* obj = ObjectWithProtoOperation(cx, state.value0);
        stack[0] = StackValue(ObjectValue(*obj));
        END_OP(ObjWithProto);
      }

        NYI_OPCODE(InitProp);
        NYI_OPCODE(InitHiddenProp);
        NYI_OPCODE(InitLockedProp);
        NYI_OPCODE(InitElem);
        NYI_OPCODE(InitHiddenElem);
        NYI_OPCODE(InitLockedElem);
        NYI_OPCODE(InitPropGetter);
        NYI_OPCODE(InitHiddenPropGetter);
        NYI_OPCODE(InitElemGetter);
        NYI_OPCODE(InitHiddenElemGetter);
        NYI_OPCODE(InitPropSetter);
        NYI_OPCODE(InitHiddenPropSetter);
        NYI_OPCODE(InitElemSetter);
        NYI_OPCODE(InitHiddenElemSetter);
        NYI_OPCODE(GetProp);
        NYI_OPCODE(GetElem);
        NYI_OPCODE(SetProp);
        NYI_OPCODE(StrictSetProp);
        NYI_OPCODE(SetElem);
        NYI_OPCODE(StrictSetElem);
        NYI_OPCODE(DelProp);
        NYI_OPCODE(StrictDelProp);
        NYI_OPCODE(DelElem);
        NYI_OPCODE(StrictDelElem);
        NYI_OPCODE(HasOwn);
        NYI_OPCODE(CheckPrivateField);
        NYI_OPCODE(NewPrivateName);
        NYI_OPCODE(SuperBase);
        NYI_OPCODE(GetPropSuper);
        NYI_OPCODE(GetElemSuper);
        NYI_OPCODE(SetPropSuper);
        NYI_OPCODE(StrictSetPropSuper);
        NYI_OPCODE(SetElemSuper);
        NYI_OPCODE(StrictSetElemSuper);
        NYI_OPCODE(Iter);
        NYI_OPCODE(MoreIter);
        NYI_OPCODE(IsNoIter);
        NYI_OPCODE(EndIter);
        NYI_OPCODE(CloseIter);
        NYI_OPCODE(CheckIsObj);
        NYI_OPCODE(CheckObjCoercible);
        NYI_OPCODE(ToAsyncIter);
        NYI_OPCODE(MutateProto);
        NYI_OPCODE(NewArray);
        NYI_OPCODE(InitElemArray);
        NYI_OPCODE(InitElemInc);
        NYI_OPCODE(Hole);
        NYI_OPCODE(RegExp);
        NYI_OPCODE(Lambda);
        NYI_OPCODE(SetFunName);
        NYI_OPCODE(InitHomeObject);
        NYI_OPCODE(CheckClassHeritage);
        NYI_OPCODE(FunWithProto);
        NYI_OPCODE(BuiltinObject);

      case JSOp::Call:
      case JSOp::CallIgnoresRv: {
        state.argc = GET_ARGC(pc.pc);
        ADVANCE(JSOpLength_Call);
        goto ic_Call;
      }

        NYI_OPCODE(CallContent);
        NYI_OPCODE(CallIter);
        NYI_OPCODE(CallContentIter);
        NYI_OPCODE(SpreadCall);
        NYI_OPCODE(OptimizeSpreadCall);
        NYI_OPCODE(Eval);
        NYI_OPCODE(SpreadEval);
        NYI_OPCODE(StrictEval);
        NYI_OPCODE(StrictSpreadEval);
        NYI_OPCODE(ImplicitThis);
        NYI_OPCODE(CallSiteObj);
        NYI_OPCODE(IsConstructing);
        NYI_OPCODE(New);
        NYI_OPCODE(NewContent);
        NYI_OPCODE(SuperCall);
        NYI_OPCODE(SpreadNew);
        NYI_OPCODE(SpreadSuperCall);
        NYI_OPCODE(SuperFun);
        NYI_OPCODE(CheckThisReinit);
        NYI_OPCODE(Generator);
        NYI_OPCODE(InitialYield);
        NYI_OPCODE(AfterYield);
        NYI_OPCODE(FinalYieldRval);
        NYI_OPCODE(Yield);
        NYI_OPCODE(IsGenClosing);
        NYI_OPCODE(AsyncAwait);
        NYI_OPCODE(AsyncResolve);
        NYI_OPCODE(Await);
        NYI_OPCODE(CanSkipAwait);
        NYI_OPCODE(MaybeExtractAwaitValue);
        NYI_OPCODE(ResumeKind);
        NYI_OPCODE(CheckResumeKind);
        NYI_OPCODE(Resume);

      case JSOp::JumpTarget:
      case JSOp::LoopHead: {
        int32_t icIndex = GET_INT32(pc.pc);
        frame->interpreterICEntry() = &frame->icScript()->icEntry(icIndex);
        END_OP(JumpTarget);
      }

      case JSOp::Goto: {
        uint32_t offset = GET_JUMP_OFFSET(pc.pc);
        ADVANCE(offset);
        break;
      }

        NYI_OPCODE(Coalesce);
        NYI_OPCODE(Case);
        NYI_OPCODE(Default);
        NYI_OPCODE(TableSwitch);

      case JSOp::Return: {
        *ret = stack.pop().asValue();
        stack.popFrame(cx);
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
        stack.popFrame(cx);
        stack.pop();  // fake return address
        return true;
      }

        NYI_OPCODE(CheckReturn);
        NYI_OPCODE(Throw);
        NYI_OPCODE(ThrowMsg);
        NYI_OPCODE(ThrowSetConst);
        NYI_OPCODE(Try);
        NYI_OPCODE(TryDestructuring);
        NYI_OPCODE(Exception);
        NYI_OPCODE(Finally);
        NYI_OPCODE(Uninitialized);
        NYI_OPCODE(InitLexical);
        NYI_OPCODE(InitGLexical);
        NYI_OPCODE(InitAliasedLexical);
        NYI_OPCODE(CheckLexical);
        NYI_OPCODE(CheckAliasedLexical);
        NYI_OPCODE(CheckThis);
        NYI_OPCODE(BindGName);
        NYI_OPCODE(BindName);
        NYI_OPCODE(GetName);

      case JSOp::GetGName: {
        state.obj0.set(&cx->global()->lexicalEnvironment());
        state.name0.set(frame->script()->getName(pc.pc));
        ADVANCE(JSOpLength_GetGName);
        goto ic_GetName;
      }

      case JSOp::GetArg: {
        unsigned i = GET_ARGNO(pc.pc);
        if (frame->script()->argsObjAliasesFormals()) {
          stack.push(StackValue(frame->argsObj().arg(i)));
        } else {
          stack.push(StackValue(frame->unaliasedFormal(i)));
        }
        END_OP(GetArg);
      }

        NYI_OPCODE(GetFrameArg);
        NYI_OPCODE(GetLocal);
        NYI_OPCODE(ArgumentsLength);
        NYI_OPCODE(GetActualArg);
        NYI_OPCODE(GetAliasedVar);
        NYI_OPCODE(GetAliasedDebugVar);
        NYI_OPCODE(GetImport);
        NYI_OPCODE(GetBoundName);
        NYI_OPCODE(GetIntrinsic);
        NYI_OPCODE(Callee);
        NYI_OPCODE(EnvCallee);
        NYI_OPCODE(SetName);
        NYI_OPCODE(StrictSetName);
        NYI_OPCODE(SetGName);
        NYI_OPCODE(StrictSetGName);
        NYI_OPCODE(SetArg);
        NYI_OPCODE(SetLocal);
        NYI_OPCODE(SetAliasedVar);
        NYI_OPCODE(SetIntrinsic);
        NYI_OPCODE(PushLexicalEnv);
        NYI_OPCODE(PopLexicalEnv);
        NYI_OPCODE(DebugLeaveLexicalEnv);
        NYI_OPCODE(RecreateLexicalEnv);
        NYI_OPCODE(FreshenLexicalEnv);
        NYI_OPCODE(PushClassBodyEnv);
        NYI_OPCODE(PushVarEnv);
        NYI_OPCODE(EnterWith);
        NYI_OPCODE(LeaveWith);
        NYI_OPCODE(BindVar);

      case JSOp::GlobalOrEvalDeclInstantiation: {
        GCThingIndex lastFun = GET_GCTHING_INDEX(pc.pc);
        state.script0 = frame->script();
        state.obj0 = frame->environmentChain();
        if (!GlobalOrEvalDeclInstantiation(cx, state.obj0, state.script0,
                                           lastFun)) {
          // TODO: exception case?
          return false;
        }
        END_OP(GlobalOrEvalDeclInstantiation);
      }

        NYI_OPCODE(DelName);
        NYI_OPCODE(Arguments);
        NYI_OPCODE(Rest);
        NYI_OPCODE(FunctionThis);

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

        NYI_OPCODE(Pick);
        NYI_OPCODE(Unpick);
        NYI_OPCODE(Lineno);
        NYI_OPCODE(NopDestructuring);
        NYI_OPCODE(ForceInterpreter);
        NYI_OPCODE(DebugCheckSelfHosted);
        NYI_OPCODE(Debugger);

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
      MOZ_CRASH("CacheIR interpreter");                               \
    }                                                                 \
  }

ic_GetName:
  printf("ic_GetName\n");
  // operand 0: envChain in state.obj0
  // payload: name in name0
  ICLOOP({
    if (!DoGetNameFallback(cx, frame, fallback, state.obj0, &state.res)) {
      return false;
    }
  });
ic_GetName_tail:
  stack.push(StackValue(state.res));
  NEXT_IC();
  goto dispatch;

ic_Call:
  printf("ic_Call\n");
  // operand 0: argc in state.argc
  ICLOOP({
    uint32_t argc = state.argc;
    uint32_t totalArgs = argc + 2;  // this, callee, func args
    Value* args = reinterpret_cast<Value*>(&stack[0]);
    // Reverse values on the stack.
    for (uint32_t i = 0; i < totalArgs / 2; i++) {
      std::swap(args[i], args[totalArgs - 1 - i]);
    }
    if (!DoCallFallback(cx, frame, fallback, argc, args, &state.res)) {
      return false;
    }
    stack.popn(totalArgs);
    stack.push(StackValue(state.res));
  });
ic_Call_tail:
  NEXT_IC();
  goto dispatch;

ic_Typeof:
  printf("ic_Typeof\n");
  // operand 0: value in state.value0
  ICLOOP({
    if (!DoTypeOfFallback(cx, frame, fallback, state.value0, &state.res)) {
      return false;
    }
  });
ic_Typeof_tail:
  stack.push(StackValue(state.res));
  NEXT_IC();
  goto dispatch;

ic_UnaryArith:
  // operand 0: value in state.value0
  printf("ic_UnaryArith\n");
  ICLOOP({
    if (!DoUnaryArithFallback(cx, frame, fallback, state.value0, &state.res)) {
      return false;
    }
  });
ic_UnaryArith_tail:
  stack.push(StackValue(state.res));
  NEXT_IC();
  goto dispatch;

ic_BinaryArith:
  printf("ic_BinaryArith\n");
  // operand 0: value in state.value0
  // operand 1: value in state.value1
  ICLOOP({
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
  printf("ic_ToBool\n");
  // operand 0: value in state.value0
  // operand 1 (some opcodes): jump offset in state.jumpOffset
  ICLOOP({
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
  printf("ic_Compare\n");
  // operand 0: value in state.value0
  // operand 1: value in state.value1
  ICLOOP({
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
  printf("ic_InstanceOf\n");
  // operand 0: value in state.value0
  // operand 1: value in state.value1
  ICLOOP({
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
  printf("ic_In\n");
  // operand 0: value in state.value0
  // operand 1: value in state.value1
  ICLOOP({
    if (!DoInFallback(cx, frame, fallback, state.value0, state.value1,
                      &state.res)) {
      return false;
    }
  });
ic_In_tail:
  stack.push(StackValue(state.res));
  NEXT_IC();
  goto dispatch;

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

  // Pop the descriptor, calleeToken, this, and args.
  stack.popn(3 + argc);

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
