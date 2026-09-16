#!/usr/bin/env node
import assert from "node:assert/strict";
import fs from "node:fs";
import vm from "node:vm";
import os from "node:os";
import path from "node:path";
import { spawnSync } from "node:child_process";
import { stripTypes } from "../tools/strip-types.mts";
import type { Ast, Expr } from "../tools/fragment.mts";
import type { SkjsClaims } from "../tools/skjs-claims.mts";
import { functionOf } from "../tools/skjs-claims.mts";
import { claimAt, expr, fn, last, stmt } from "./edits.mts";

/** A call, which is what every alteration below changes. */
type Call = Extract<Expr, { k: "apply" }>;

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
/** The call this fixture is about: the one its body ends with. */
const order = (a: Ast) => expr(stmt(last(fn(a, "argumentOrder").body), "return").e, "apply");
const work = fs.mkdtempSync(path.join(os.tmpdir(), "callable-arity-"));
try {
  const ast: Ast = JSON.parse(fs.readFileSync(astPath, "utf8"));
  const claims: SkjsClaims = JSON.parse(fs.readFileSync(claimsPath, "utf8"));
  const input = path.join(work, "ast"), contract = path.join(work, "claims");
  const evidence = path.join(work, "evidence");
  const verify = (mode: string, a: Ast, c: SkjsClaims) => {
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
  order(swapped).args.reverse();
  assert.notEqual(verify("--check-stateful-source", swapped, claims).status, 0,
    "saved evidence must not accept reversed actuals with the same types");
  for (const edit of [
    (c: Call) => { c.args.pop(); },
    (c: Call) => { c.args.push(structuredClone(c.args[0])); },
  ]) {
    const changed = structuredClone(ast);
    edit(order(changed));
    for (const mode of ["--check-stateful-source", "--produce-stateful-source"])
      assert.notEqual(verify(mode, changed, claims).status, 0, "actual count must match");
  }

  const badArgument = structuredClone(ast), badClaims = structuredClone(claims);
  const badCall = order(badArgument);
  const secondPos = badCall.args[1].pos;
  badCall.args[1] = {k: "lit", pos: secondPos, lit: {a: "null"}};
  claimAt(functionOf(badClaims, file, "argumentOrder"), secondPos).type =
    {top: false, atoms: [{a: "null"}]};
  for (const mode of ["--check-stateful-source", "--produce-stateful-source"])
    assert.notEqual(verify(mode, badArgument, badClaims).status, 0, "later actual must satisfy its own domain");
  console.log("  native source argument lists: original evidence, order binding and exact arity OK");
} finally {
  fs.rmSync(work, {recursive: true, force: true});
}
