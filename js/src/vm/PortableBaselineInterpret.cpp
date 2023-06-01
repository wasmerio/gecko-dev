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
    if (reinterpret_cast<uintptr_t>(base) + size > reinterpret_cast<uintptr_t>(*sp)) {
      return nullptr;
    }
    (*sp) = reinterpret_cast<StackValue*>(reinterpret_cast<uintptr_t>(*sp) - size);
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

    BaselineFrame* frame = reinterpret_cast<BaselineFrame*>(allocate(BaselineFrame::Size()));
    if (!frame) {
      return nullptr;
    }

    frame->setFlags(BaselineFrame::Flags::RUNNING_IN_INTERPRETER);
    frame->setEnvironmentChain(envChain);
    frame->setInterpreterFields(frame->script()->code());

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
    return reinterpret_cast<BaselineFrame*>(reinterpret_cast<uintptr_t>(fp) - BaselineFrame::Size());
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
  jsbytecode** pc = &frame->interpreterPC();
  
  while(true) {
    printf("pc = %p: %d\n", *pc, **pc);
    switch (JSOp(**pc)) {
    case JSOp::Nop:
      (*pc)++;
      break;
    default:
      MOZ_CRASH("Bad opcode");
    }
  }

  return true;
}

bool js::PortableBaselineTrampoline(JSContext* cx, size_t argc, Value* argv,
                                    CalleeToken calleeToken,
                                    JSObject* envChain, Value* result) {
  Stack stack(cx->portableBaselineStack());

  printf("Trampoline: argc %zu argv %p calleeToken %p\n", argc, argv, calleeToken);

  // Expected stack frame:
  // - argN
  // - ...
  // - arg1
  // - this
  // - calleeToken
  // - descriptor
  // - "return address" (nullptr for top frame)

  for (ssize_t i = argc; i >= 0; --i) {
    stack.push(StackValue(argv[argc]));
  }
  stack.push(StackValue(calleeToken));
  stack.push(StackValue(
      MakeFrameDescriptorForJitCall(FrameType::CppToJSJit, argc)));
  const uint64_t ra = 0;  // return address
  stack.push(StackValue(ra));

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
