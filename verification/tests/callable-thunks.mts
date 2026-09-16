#!/usr/bin/env node
import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import vm from "node:vm";
import { spawnSync } from "node:child_process";
import { stripTypes } from "../tools/strip-types.mts";
import type { Ast } from "../tools/fragment.mts";
import type { ClaimType } from "../tools/claim.mts";
import { functionOf, type SkjsClaims } from "../tools/skjs-claims.mts";
import { atom, claimAt, claimType, expr, fn, last, rows, stmt } from "./edits.mts";

const [astPath, claimsPath, file, verifier] = process.argv.slice(2);
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "callable-thunks-"));
try {
  const source: Ast = JSON.parse(fs.readFileSync(astPath, "utf8"));
  const claims: SkjsClaims = JSON.parse(fs.readFileSync(claimsPath, "utf8"));
  const astFile = path.join(tmp, "ast"), claimsFile = path.join(tmp, "claims");
  const evidence = path.join(tmp, "evidence");
  const run = (mode: string, ast: Ast, supplied: SkjsClaims) => {
    fs.writeFileSync(astFile, JSON.stringify(ast));
    fs.writeFileSync(claimsFile, JSON.stringify(supplied));
    const result = spawnSync(verifier, [mode, astFile, claimsFile, file, evidence,
      ...(mode === "--produce-stateful-source" ? ["10"] : [])], {encoding: "utf8", timeout: 30000});
    assert(!result.error && !result.signal, String(result.error || result.signal));
    return result;
  };
  for (const mode of ["--produce-stateful-source", "--check-stateful-source"]) {
    const result = run(mode, source, claims);
    assert.equal(result.status, 0, result.stdout + result.stderr);
  }
  const thunk = fn(source, "returnedThunk");
  const call = expr(stmt(last(thunk.body), "return").e, "apply");
  assert.deepEqual(call.args, []);
  for (const [name, edit] of rows<[string, (type: ClaimType) => void]>([
    ["omission cannot supply a Boolean argument", (type) => {
      atom(type.atoms[0], "function").params = [{top: false, atoms: [{a: "boolean"}]}];
    }],
    ["a thunk cannot promise an incompatible result", (type) => {
      atom(type.atoms[0], "function").result = {top: false, atoms: [{a: "null"}]};
    }],
  ])) {
    const changed = structuredClone(claims);
    const claim = claimAt(functionOf(changed, file, thunk.name), call.callee.pos);
    edit(claimType(claim));
    for (const mode of ["--check-stateful-source", "--produce-stateful-source"]) {
      const result = run(mode, source, changed);
      assert.notEqual(result.status, 0, `${name}: ${mode} accepted the forged contract`);
    }
  }
  const context = vm.createContext({});
  vm.runInContext(stripTypes(fs.readFileSync(file, "utf8")), context, {timeout: 1000});
  for (const seed of [false, true]) {
    assert.equal(vm.runInContext(`returnedThunk(${seed})`, context, {timeout: 1000}), !seed);
    assert.equal(vm.runInContext(`storedThunk(${seed})`, context, {timeout: 1000}), true);
  }
  console.log("  thunks: original claims, independent checking, rejected forgery and delayed-read witnesses OK");
} finally {
  fs.rmSync(tmp, {recursive: true, force: true});
}
