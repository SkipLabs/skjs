#!/usr/bin/env node
import assert from "node:assert/strict";
import fs from "node:fs";
import vm from "node:vm";
import os from "node:os";
import path from "node:path";
import { spawnSync } from "node:child_process";
import { stripTypes } from "../tools/strip-types.mts";

// The existing order-sensitive witness now goes through the source pipeline.
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
console.log("  argument order: callee first and left-to-right arguments distinguished; JavaScript controls OK");

const [astPath, claimsPath, file, verifier] = process.argv.slice(2);
const work = fs.mkdtempSync(path.join(os.tmpdir(), "callable-arity-"));
try {
  const ast = JSON.parse(fs.readFileSync(astPath, "utf8"));
  const claims = JSON.parse(fs.readFileSync(claimsPath, "utf8"));
  const input = path.join(work, "ast"), contract = path.join(work, "claims");
  const evidence = path.join(work, "evidence");
  const verify = (mode: string, a: any, c: any) => {
    fs.writeFileSync(input, JSON.stringify(a));
    fs.writeFileSync(contract, JSON.stringify(c));
    const args = [mode, input, contract, file, evidence];
    if (mode === "--produce-stateful-source") args.push("10");
    const r = spawnSync(verifier, args, {encoding: "utf8"});
    if (r.error || r.signal) throw r.error || Error(String(r.signal));
    return r;
  };
  for (const mode of ["--produce-stateful-source", "--check-stateful-source"]) {
    const r = verify(mode, ast, claims);
    assert.equal(r.status, 0, r.stdout + r.stderr);
  }
  const swapped = structuredClone(ast);
  const call = swapped.functions.find((f: any) => f.name === "argumentOrder").body.at(-1).e;
  call.args.reverse();
  assert.notEqual(verify("--check-stateful-source", swapped, claims).status, 0,
    "saved evidence must not accept reversed actuals with the same types");
  for (const edit of [
    (c: any) => { c.args.pop(); },
    (c: any) => { c.args.push(structuredClone(c.args[0])); },
  ]) {
    const changed = structuredClone(ast);
    edit(changed.functions.find((f: any) => f.name === "argumentOrder").body.at(-1).e);
    for (const mode of ["--check-stateful-source", "--produce-stateful-source"])
      assert.notEqual(verify(mode, changed, claims).status, 0, "actual count must match");
  }

  const badArgument = structuredClone(ast), badClaims = structuredClone(claims);
  const badCall = badArgument.functions.find((f: any) => f.name === "argumentOrder").body.at(-1).e;
  const secondPos = badCall.args[1].pos;
  badCall.args[1] = {k: "lit", pos: secondPos, lit: {a: "null"}};
  const fc = badClaims.find((b: any) => b.file === file).functions.find((f: any) => f.name === "argumentOrder");
  fc.exprs.find((e: any) => e.pos[0] === secondPos[0] && e.pos[1] === secondPos[1]).type =
    {top: false, atoms: [{a: "null"}]};
  for (const mode of ["--check-stateful-source", "--produce-stateful-source"])
    assert.notEqual(verify(mode, badArgument, badClaims).status, 0, "later actual must satisfy its own domain");
  console.log("  native source argument lists: original evidence, order binding and exact arity OK");
} finally {
  fs.rmSync(work, {recursive: true, force: true});
}
