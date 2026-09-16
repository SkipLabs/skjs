#!/usr/bin/env node
import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { spawnSync } from "node:child_process";
import vm from "node:vm";
import { stripTypes } from "../tools/strip-types.mts";
import type { Ast } from "../tools/fragment.mts";
import type { ClaimType } from "../tools/claim.mts";
import { functionOf, type SkjsClaims, type SkjsFunction } from "../tools/skjs-claims.mts";
import { at as nth, atom, claimAt, claimType, expr, fn as functionIn, last, must, rows, stmt } from "./edits.mts";

const [astPath, claimsPath, file, verifier] = process.argv.slice(2);
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "callable-arguments-"));
try {
  const source: Ast = JSON.parse(fs.readFileSync(astPath, "utf8"));
  const exported: SkjsClaims = JSON.parse(fs.readFileSync(claimsPath, "utf8"));
  const fn = functionIn(source, "callableArgument");
  /** The call whose argument is the callback under test. */
  const invocation = (f = fn) => expr(stmt(nth(f.body, 3), "const").init, "apply");
  const ast = path.join(tmp, "ast"), claims = path.join(tmp, "claims");
  const evidence = path.join(tmp, "evidence");
  const run = (mode: string, a: Ast, c: SkjsClaims) => {
    fs.writeFileSync(ast, JSON.stringify(a));
    fs.writeFileSync(claims, JSON.stringify(c));
    const args = [mode, ast, claims, file, evidence];
    if (mode === "--produce-stateful-source") args.push("10");
    const result = spawnSync(verifier, args, {encoding: "utf8"});
    if (result.error || result.signal) throw result.error || Error(String(result.signal));
    return result;
  };
  for (const mode of ["--produce-stateful-source", "--check-stateful-source"]) {
    const result = run(mode, source, exported);
    assert.equal(result.status, 0, result.stdout + result.stderr);
  }
  console.log("  stateful callable arguments: original claims and independent consumer OK");

  const transported = functionIn(source, "exchangeMultiArgument");
  const returned = stmt(last(transported.body), "return").e;
  for (const [name, domains] of rows<[string, ClaimType[]]>([
    ["later parameter cannot widen from null to Boolean",
      [{top: false, atoms: [{a: "boolean"}]}, {top: false, atoms: [{a: "boolean"}]}]],
    ["a native signature cannot lose its second parameter",
      [{top: false, atoms: [{a: "boolean"}]}]],
  ])) {
    const changed = structuredClone(exported);
    const fc = functionOf(changed, file, transported.name);
    atom(claimType(claimAt(fc, returned.pos)).atoms[0], "function").params = domains;
    for (const mode of ["--check-stateful-source", "--produce-stateful-source"]) {
      const result = run(mode, source, changed);
      assert.notEqual(result.status, 0, name);
    }
  }
  console.log("  transported multi-argument contracts retain later domains and arity: OK");
  const omitted = structuredClone(source);
  invocation(functionIn(omitted, "callableArgument")).args = [];
  for (const mode of ["--check-stateful-source", "--produce-stateful-source"]) {
    const result = run(mode, omitted, exported);
    assert.notEqual(result.status, 0, "omission cannot satisfy a required callback parameter");
  }
  console.log("  omitted required callback argument: rejected by production and independent consumer");
  const runtime = vm.createContext({});
  vm.runInContext(stripTypes(fs.readFileSync(file, "utf8")), runtime, {timeout: 1000});
  for (const seed of [false, true])
    assert.equal(vm.runInContext(`escapedCallbackArgument(${seed})`, runtime, {timeout: 1000}), !seed);
  const escaped = functionIn(source, "escapedCallbackArgument");
  const terminal = stmt(last(escaped.body), "return");
  const original = fs.readFileSync(file, "utf8");
  const observations: boolean[][] = [];
  const observed = vm.createContext({observe: (...values: boolean[]) => { observations.push(values); }});
  vm.runInContext(stripTypes(original.slice(0, terminal.pos[0]) +
    "observe(old, cell.value); " + original.slice(terminal.pos[0])), observed, {timeout: 1000});
  for (const seed of [false, true])
    vm.runInContext(`escapedCallbackArgument(${seed})`, observed, {timeout: 1000});
  assert.deepEqual(observations, [[true, false], [false, true]]);
  console.log("  escaped callback argument observes the write and forwards the argument: JavaScript witness OK");
  for (const [name, change] of rows<[string, (fc: SkjsFunction) => void]>([
    ["callback must accept the invoker's full Boolean domain", (fc) => {
      const arg = must(invocation().args[0], "an argument");
      atom(claimType(claimAt(fc, arg.pos)).atoms[0], "function").params[0] =
        {top: false, atoms: [{a: "booleanlit", v: "false"}]};
    }],
    ["invoker cannot accept callbacks with incompatible results", (fc) => {
      const callee = invocation().callee;
      const invoker = atom(claimType(claimAt(fc, callee.pos)).atoms[0], "function");
      atom(must(invoker.params[0], "a domain").atoms[0], "function").result =
        {top: false, atoms: [{a: "null"}]};
    }],
  ])) {
    const changed = structuredClone(exported);
    change(functionOf(changed, file, fn.name));
    // Check reuse first so a failed production cannot alter the original evidence.
    for (const mode of ["--check-stateful-source", "--produce-stateful-source"]) {
      const result = run(mode, source, changed);
      assert.notEqual(result.status, 0, `${name}: ${mode} accepted forged contract`);
    }
    console.log(`  ${name}: OK`);
  }
} finally {
  fs.rmSync(tmp, {recursive: true, force: true});
}
