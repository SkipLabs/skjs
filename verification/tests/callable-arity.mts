#!/usr/bin/env node
import assert from "node:assert/strict";
import fs from "node:fs";
import vm from "node:vm";
import { stripTypes } from "../tools/strip-types.mts";

// The TypeScript-claims suite records this file's current source gate. This
// runtime witness fixes the required behavior before argument-list integration.
const source = fs.readFileSync("verification/tests/callables/arity.ts", "utf8");
const run = (text: string) => {
  const context = vm.createContext({});
  vm.runInContext(stripTypes(text), context, {timeout: 1000});
  return vm.runInContext("argumentOrder()", context, {timeout: 1000});
};
assert.equal(run(source), true);
// Swapping evaluation while preserving parameter positions changes the heap
// seen by both arguments and the body. This control detects an insensitive test.
const terminal = "return choose()(first(), second());";
assert(source.includes(terminal));
assert.equal(run(source.replace(terminal,
  "const callee = choose(); const b = second(); const a = first(); return callee(a, b);")), false);
assert.equal(run(source.replace(terminal,
  "const a = first(); const b = second(); return choose()(a, b);")), false);
console.log("  argument order: callee first and left-to-right arguments distinguished; source integration remains gated");
