#!/usr/bin/env node
import assert from "node:assert/strict";
import fs from "node:fs";
import path from "node:path";
import vm from "node:vm";
import { spawnSync } from "node:child_process";
import { stripTypes } from "../tools/strip-types.mts";

const file = "verification/tests/callables/call-objects.ts";
const source = fs.readFileSync(file, "utf8");
const check = spawnSync(path.resolve("verification/tools/node_modules/.bin/tsc"),
  ["--strict", "--noEmit", "--target", "es2020", "--skipLibCheck", file], {encoding: "utf8"});
assert(!check.error && !check.signal, String(check.error || check.signal));
assert.equal(check.status, 0, check.stdout + check.stderr);
const parsed = spawnSync(process.execPath, ["verification/tools/parse-source.mts", file], {encoding: "utf8"});
assert(!parsed.error && !parsed.signal, String(parsed.error || parsed.signal));
assert.equal(parsed.status, 1);
assert.match(parsed.stderr, /expected plain single-field allocation/);

const results = (text: string) => {
  const context = vm.createContext({});
  vm.runInContext(stripTypes(text), context, {timeout: 1000});
  return [false, true].map(seed => vm.runInContext(`callObjects(${seed})`, context, {timeout: 1000}));
};
assert.deepEqual(results(source), [true, true]);
const call = "method.call(receiver, true, false)";
assert(source.includes(call));
assert.deepEqual(results(source.replace(call, "method.call(owner, true, false)")), [false, false]);
const arrow = "read: (): boolean => seed";
assert(source.includes(arrow));
assert.deepEqual(results(source.replace(arrow,
  "read(this: { value: boolean }): boolean { return this.value; }")), [false, false]);
console.log("  explicit receiver and lexical arrow capture distinguished for both seeds; source boundary retained");
