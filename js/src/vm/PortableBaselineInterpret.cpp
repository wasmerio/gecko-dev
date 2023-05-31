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

#include "jit/BaselineJIT.h"
#include "jit/JitFrames.h"
#include "jit/JitScript.h"
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
  explicit StackValue(jit::CalleeToken v)
      : value(reinterpret_cast<uint64_t>(v)) {}

  uint64_t asUInt64() const { return value; }
  Value asValue() const { return Value::fromRawBits(value); }
  jit::CalleeToken asCalleeToken() const {
    return reinterpret_cast<jit::CalleeToken>(value);
  }
};

struct Stack {
  StackValue* sp;
  StackValue* base;

  Stack(uint64_t* sp_, uint64_t* base_)
      : sp(reinterpret_cast<StackValue*>(sp_)),
        base(reinterpret_cast<StackValue*>(base_)) {}

  bool push(StackValue v) {
    if (sp <= base) {
      return false;
    }
    *--sp = v;
    return true;
  }
  StackValue pop() { return *sp++; }
};

// TODO:
// - put SP state in PortableBaselineStack and update it in trampoline
//   (pre + post).
// - update GC scanning to scan PortableBaselineStack.
// - create a BaselineFrame in PortableBaselineInterpret, and root
//   everything on that (JSScript, JitScript).
// - opcode dispatch based on current interpreter PC in BaselineFrame.
// - IC interpreter state (current stub and IC PC).

static bool js::PortableBaselineInterpret(JSContext* cx, Stack& stack,
                                          Value* ret) {
  
}

bool js::PortableBaselineTrampoline(JSContext* cx, size_t argc, Value* argv,
                                    jit::CalleeToken calleeToken,
                                    JSObject* envChain, Value* result,
                                    // TODO: take PortableBaselineStack
                                    uint64_t* sp, uint64_t* spBase) {
  Stack stack(sp, spBase);
  uint64_t* fp = stack.sp;

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
      jit::MakeFrameDescriptorForJitCall(jit::FrameType::CppToJSJit, argc)));
  stack.push(0);  // return address

  if (!PortableBaselineInterpret(cx, stack, result)) {
    return false;
  }

  // TODO: save SP in portableBaselineStack.

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
