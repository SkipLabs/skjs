#!/usr/bin/env node
/*
 * call-objects.ts: an ordinary method rebound with `.call`, and an arrow whose
 * `.call` receiver is ignored. It runs as the source says, and both the
 * TypeScript and the OCaml producers' claims verify.
 */
import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import vm from "node:vm";
import { spawnSync } from "node:child_process";
import { stripTypes } from "../tools/strip-types.mts";
import { check as ocamlCheck } from "../ocaml-producer/check.mts";

const [verifier] = process.argv.slice(2);
const file = "verification/tests/callables/call-objects.ts";
const source = fs.readFileSync(file, "utf8");
const check = spawnSync(path.resolve("verification/tools/node_modules/.bin/tsc"),
  ["--strict", "--noEmit", "--target", "es2020", "--skipLibCheck", file], {encoding: "utf8"});
assert(!check.error && !check.signal, String(check.error || check.signal));
assert.equal(check.status, 0, check.stdout + check.stderr);

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
console.log("  explicit receiver and lexical arrow capture distinguished for both seeds: OK");

const work = fs.mkdtempSync(path.join(os.tmpdir(), "call-objects-"));
try {
  const run = (cmd: string, args: string[]) => {
    const r = spawnSync(cmd, args, {encoding: "utf8", timeout: 120000});
    if (r.error || r.signal) throw r.error || Error(String(r.signal));
    return r;
  };
  const ast = path.join(work, "ast.json"), claims = path.join(work, "claims.json"),
    evidence = path.join(work, "evidence.json");
  const parsed = run(process.execPath, ["verification/tools/fragment-parse.mts", file]);
  assert.equal(parsed.status, 0, parsed.stderr);
  fs.writeFileSync(ast, parsed.stdout);
  const produced = run(process.execPath, ["verification/tools/tsc-claims.mts", file, "--out", claims]);
  assert.equal(produced.status, 0, produced.stderr);
  const proved = run(verifier, ["--produce-source-claims", ast, claims, file, evidence, "10"]);
  assert.equal(proved.status, 0, proved.stdout + proved.stderr);
  const consumed = run(verifier, ["--check-source-claims", ast, claims, file, evidence]);
  assert.equal(consumed.status, 0, consumed.stdout + consumed.stderr);
  console.log("  TypeScript producer's claims produced and independently consumed: OK");
  const ocaml = ocamlCheck(file);
  assert.equal(ocaml.status, "verified", JSON.stringify(ocaml));
  console.log("  OCaml producer's claims verified: OK");
  // Without the strict directive the method's `this` would be the global
  // object on a plain call; the verifier refuses the sloppy method.
  const sloppy = path.join(work, "sloppy.ts");
  fs.writeFileSync(sloppy, source.replace('"use strict";\n', ""));
  fs.writeFileSync(path.join(work, "tsconfig.json"),
    JSON.stringify({compilerOptions: {strict: true}, files: ["sloppy.ts"]}));
  const sloppyAst = path.join(work, "sloppy.ast.json");
  const reparsed = run(process.execPath, ["verification/tools/fragment-parse.mts", sloppy]);
  assert.equal(reparsed.status, 0, reparsed.stderr);
  fs.writeFileSync(sloppyAst, reparsed.stdout);
  const sloppyClaims = path.join(work, "sloppy.claims.json");
  const reproduced = run(process.execPath, ["verification/tools/tsc-claims.mts", sloppy, "--out", sloppyClaims]);
  assert.equal(reproduced.status, 0, reproduced.stderr);
  const rejected = run(verifier, ["--produce-source-claims", sloppyAst, sloppyClaims, sloppy, evidence, "10"]);
  assert.notEqual(rejected.status, 0);
  assert.match(rejected.stdout + rejected.stderr, /a function that reads `this` must be strict code/);
  console.log("  the method in sloppy code is refused: OK");
} finally {
  fs.rmSync(work, {recursive: true, force: true});
}
