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
#include "jit/JitScript.h"
#include "vm/JSScript.h"
#include "vm/Opcodes.h"

#include "jit/JitScript-inl.h"
#include "vm/JSScript-inl.h"

using namespace js;
using namespace js::jit;

bool js::PortableBaselineInterpret(JSContext* cx, RunState& state) { return false; }

bool js::CanEnterPortableBaselineInterpreter(JSContext* cx, JSScript* script) {
  if (!JitOptions.portableBaselineInterpreter) {
    return false;
  }
  if (script->hasJitScript()) {
    return true;
  }
  if (script->hasForceInterpreterOp()) {
    return false;
  }
  if (script->getWarmUpCount() <=
      JitOptions.portableBaselineInterpreterWarmUpThreshold) {
    return false;
  }
  if (!cx->realm()->ensureJitRealmExists(cx)) {
    return false;
  }

  AutoKeepJitScripts keepJitScript(cx);
  if (!script->ensureHasJitScript(cx, keepJitScript)) {
    return false;
  }
  return true;
}
