#!/usr/bin/env node
import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import vm from "node:vm";
import { spawnSync } from "node:child_process";
import { stripTypes } from "../tools/strip-types.mts";
import type { Ast, Expr } from "../tools/fragment.mts";
import { functionOf, type SkjsClaims } from "../tools/skjs-claims.mts";
import { claimAt, expr, last, stmt } from "./edits.mts";

const [astPath, claimsPath, file, verifier] = process.argv.slice(2);
/** The call with a receiver this fixture ends with. */
type Received = Extract<Expr, { k: "callWithReceiver" | "bindWithReceiver" }>;
const received = (a: Ast): Received =>
  expr(stmt(last(a.functions[0].body), "return").e, "callWithReceiver");
const work = fs.mkdtempSync(path.join(os.tmpdir(), "receiver-call-"));
try {
  const source = fs.readFileSync(file, "utf8");
  const execute = (text: string, expression: string) => {
    const context = vm.createContext({});
    vm.runInContext(stripTypes(text), context, {timeout: 1000});
    return vm.runInContext(expression, context, {timeout: 1000});
  };
  for (const seed of [false, true]) {
    assert.equal(execute(source, `receiverCall(${seed})`), false);
    assert.equal(execute(source, `capturedReceiverCall(${seed})`), !seed);
    const omitted = source.replace("(alias.value = !seed),", "seed,");
    assert.notEqual(omitted, source);
    assert.equal(execute(omitted, `receiverCall(${seed})`), true);
    const late = source.replace("return alias.call((alias.value = !seed), alias.value, seed);",
      "const first = alias.value; const second = seed; alias.value = !seed; return alias.call(null, first, second);");
    assert.notEqual(late, source);
    assert.equal(execute(late, `receiverCall(${seed})`), true);
  }

  const ast: Ast = JSON.parse(fs.readFileSync(astPath, "utf8"));
  const claims: SkjsClaims = JSON.parse(fs.readFileSync(claimsPath, "utf8"));
  const input = path.join(work, "ast"), contract = path.join(work, "claims"), evidence = path.join(work, "evidence");
  const check = (mode: string, a: Ast, c: SkjsClaims) => {
    fs.writeFileSync(input, JSON.stringify(a));
    fs.writeFileSync(contract, JSON.stringify(c));
    const args = [mode, input, contract, file, evidence];
    if (mode === "--produce-stateful-source") args.push("10");
    const r = spawnSync(verifier, args, {encoding: "utf8"});
    if (r.error || r.signal) throw r.error || Error(String(r.signal));
    return r;
  };
  for (const mode of ["--produce-stateful-source", "--check-stateful-source"]) {
    const r = check(mode, ast, claims);
    assert.equal(r.status, 0, r.stdout + r.stderr);
  }
  const changed = structuredClone(ast);
  const call = received(changed);
  // A same-typed inert receiver must not reuse evidence for its original write.
  call.receiver = {k: "lit", pos: call.receiver.pos, lit: {a: "booleanlit", v: "true"}};
  assert.notEqual(check("--check-stateful-source", changed, claims).status, 0);
  for (const edit of [
    (c: Received) => c.args.unshift(c.receiver),
    (c: Received) => c.args.pop(),
  ]) {
    const a = structuredClone(ast);
    edit(received(a));
    for (const mode of ["--check-stateful-source", "--produce-stateful-source"])
      assert.notEqual(check(mode, a, claims).status, 0, "receiver is excluded from exact actual count");
  }
  const bad = structuredClone(claims);
  const pos = received(ast).receiver.pos;
  claimAt(functionOf(bad, file, "receiverCall"), pos).type =
    {top: false, atoms: [{a: "null"}]};
  for (const mode of ["--check-stateful-source", "--produce-stateful-source"])
    assert.notEqual(check(mode, ast, bad).status, 0, "discarding a receiver value does not discard its claim");

  const probes = [
    "function f(g: (x: boolean) => boolean): boolean { return g.call(null, true); }",
    "function f(): boolean { const g = (): boolean => true; return ((g: () => boolean): boolean => g.call(null))((): boolean => false); }",
    "function f(factory: () => (() => boolean)): boolean { return factory().call(null); }",
    "function f(): boolean { const g = (): boolean => true; return g.call(); }",
  ];
  for (const text of probes) {
    const probe = path.join(work, "probe.ts");
    fs.writeFileSync(probe, text);
    const r = spawnSync(process.execPath, ["verification/tools/fragment-parse.mts", probe], {encoding: "utf8"});
    if (r.error || r.signal) throw r.error || Error(String(r.signal));
    assert.notEqual(r.status, 0, text);
    assert.match(r.stderr, /\.call requires a known local function/);
  }
  console.log("  local arrow .call: receiver effects, captured thunk, checked claims, exact arity and intrinsic provenance OK");
} finally {
  fs.rmSync(work, {recursive: true, force: true});
}
