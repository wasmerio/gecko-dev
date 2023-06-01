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
#include "jit/BaselineJIT.h"
#include "jit/JitFrames.h"
#include "jit/JitScript.h"
#include "jit/JSJitFrameIter.h"
#include "vm/JitActivation.h"
#include "vm/JSScript.h"
#include "vm/Opcodes.h"

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

  StackValue* cur() { return *sp; }
  void restore(StackValue* s) { *sp = s; }

  BaselineFrame* pushFrame(JSContext* cx, void* retAddr, JSObject* envChain) {
    if (!push(StackValue(retAddr))) {
      return nullptr;
    }
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

  void popFrame(JSContext* cx, void** retAddr) {
    StackValue* newTOS = &fp[2];
    *retAddr = fp[1].asVoidPtr();
    fp = reinterpret_cast<StackValue*>(fp[0].asVoidPtr());

    cx->activation()->asJit()->setJSExitFP(reinterpret_cast<uint8_t*>(fp));

    restore(newTOS);
  }

  BaselineFrame* frameFromFP() {
    return reinterpret_cast<BaselineFrame*>(reinterpret_cast<uintptr_t>(fp) -
                                            BaselineFrame::Size());
  }
};

// TODO:
// - update GC scanning to scan PortableBaselineStack.
// - create a BaselineFrame in PortableBaselineInterpret, and root
//   everything on that (JSScript, JitScript).
// - opcode dispatch based on current interpreter PC in BaselineFrame.
// - IC interpreter state (current stub and IC PC).

static bool PortableBaselineInterpret(JSContext* cx, Stack& stack, Value* ret) {
  BaselineFrame* frame = stack.frameFromFP();

  while (true) {
    jsbytecode*& pc = frame->interpreterPC();
    printf("pc = %p: %d\n", pc, *pc);

#define NYI_OPCODE(op)                               \
  case JSOp::op:                                     \
    printf("not-yet-implemented opcode: " #op "\n"); \
    MOZ_CRASH("Bad opcode");                         \
    break;

    switch (JSOp(*pc)) {
      case JSOp::Nop:
        pc++;
        break;

        NYI_OPCODE(Undefined);
        NYI_OPCODE(Null);
        NYI_OPCODE(False);
        NYI_OPCODE(True);
        NYI_OPCODE(Int32);
        NYI_OPCODE(Zero);
        NYI_OPCODE(One);
        NYI_OPCODE(Int8);
        NYI_OPCODE(Uint16);
        NYI_OPCODE(Uint24);
        NYI_OPCODE(Double);
        NYI_OPCODE(BigInt);
        NYI_OPCODE(String);
        NYI_OPCODE(Symbol);
        NYI_OPCODE(Void);
        NYI_OPCODE(Typeof);
        NYI_OPCODE(TypeofExpr);
        NYI_OPCODE(Pos);
        NYI_OPCODE(Neg);
        NYI_OPCODE(BitNot);
        NYI_OPCODE(Not);
        NYI_OPCODE(BitOr);
        NYI_OPCODE(BitXor);
        NYI_OPCODE(BitAnd);
        NYI_OPCODE(Eq);
        NYI_OPCODE(Ne);
        NYI_OPCODE(StrictEq);
        NYI_OPCODE(StrictNe);
        NYI_OPCODE(Lt);
        NYI_OPCODE(Gt);
        NYI_OPCODE(Le);
        NYI_OPCODE(Ge);
        NYI_OPCODE(Instanceof);
        NYI_OPCODE(In);
        NYI_OPCODE(Lsh);
        NYI_OPCODE(Rsh);
        NYI_OPCODE(Ursh);
        NYI_OPCODE(Add);
        NYI_OPCODE(Sub);
        NYI_OPCODE(Inc);
        NYI_OPCODE(Dec);
        NYI_OPCODE(Mul);
        NYI_OPCODE(Div);
        NYI_OPCODE(Mod);
        NYI_OPCODE(Pow);
        NYI_OPCODE(ToPropertyKey);
        NYI_OPCODE(ToNumeric);
        NYI_OPCODE(ToString);
        NYI_OPCODE(IsNullOrUndefined);
        NYI_OPCODE(GlobalThis);
        NYI_OPCODE(NonSyntacticGlobalThis);
        NYI_OPCODE(NewTarget);
        NYI_OPCODE(DynamicImport);
        NYI_OPCODE(ImportMeta);
        NYI_OPCODE(NewInit);
        NYI_OPCODE(NewObject);
        NYI_OPCODE(Object);
        NYI_OPCODE(ObjWithProto);
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
        NYI_OPCODE(Call);
        NYI_OPCODE(CallContent);
        NYI_OPCODE(CallIter);
        NYI_OPCODE(CallContentIter);
        NYI_OPCODE(CallIgnoresRv);
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
        NYI_OPCODE(JumpTarget);
        NYI_OPCODE(LoopHead);
        NYI_OPCODE(Goto);
        NYI_OPCODE(JumpIfFalse);
        NYI_OPCODE(JumpIfTrue);
        NYI_OPCODE(And);
        NYI_OPCODE(Or);
        NYI_OPCODE(Coalesce);
        NYI_OPCODE(Case);
        NYI_OPCODE(Default);
        NYI_OPCODE(TableSwitch);
        NYI_OPCODE(Return);
        NYI_OPCODE(GetRval);
        NYI_OPCODE(SetRval);
        NYI_OPCODE(RetRval);
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
        NYI_OPCODE(GetGName);
        NYI_OPCODE(GetArg);
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
        NYI_OPCODE(GlobalOrEvalDeclInstantiation);
        NYI_OPCODE(DelName);
        NYI_OPCODE(Arguments);
        NYI_OPCODE(Rest);
        NYI_OPCODE(FunctionThis);
        NYI_OPCODE(Pop);
        NYI_OPCODE(PopN);
        NYI_OPCODE(Dup);
        NYI_OPCODE(Dup2);
        NYI_OPCODE(DupAt);
        NYI_OPCODE(Swap);
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

  return true;
}

bool js::PortableBaselineTrampoline(JSContext* cx, size_t argc, Value* argv,
                                    CalleeToken calleeToken, JSObject* envChain,
                                    Value* result) {
  Stack stack(cx->portableBaselineStack());

  printf("Trampoline: argc %zu argv %p calleeToken %p\n", argc, argv,
         calleeToken);

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

  if (!stack.pushFrame(cx, /* retAddr = */ nullptr, envChain)) {
    return false;
  }

  if (!PortableBaselineInterpret(cx, stack, result)) {
    return false;
  }

  void* dummyRet;
  stack.popFrame(cx, &dummyRet);
  MOZ_ASSERT(dummRet == nullptr);

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
