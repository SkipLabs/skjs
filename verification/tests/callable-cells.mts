#!/usr/bin/env node
import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import vm from "node:vm";
import { spawnSync } from "node:child_process";
import { stripTypes } from "../tools/strip-types.mts";

const [astPath, claimsPath, file, verifier] = process.argv.slice(2);
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "callable-cells-"));
try {
  const source = JSON.parse(fs.readFileSync(astPath, "utf8"));
  const claims = JSON.parse(fs.readFileSync(claimsPath, "utf8"));
  const astFile = path.join(tmp, "ast"), claimsFile = path.join(tmp, "claims");
  const evidence = path.join(tmp, "evidence");
  const run = (mode: string, ast: any, supplied: any) => {
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
  for (const [name, mutate] of [
    ["callable storage must retain its full argument domain", (field: any) => {
      field.read.atoms[0].params[0] = {top: false, atoms: [{a: "booleanlit", v: "true"}]};
    }],
    ["a replacement cannot change the stored result contract", (field: any) => {
      field.read.atoms[0].result = {top: false, atoms: [{a: "null"}]};
      field.write = structuredClone(field.read);
    }],
  ] as [string, (field: any) => void][]) {
    const changed = structuredClone(claims);
    const fn = source.functions.find((f: any) => f.name === "replacedCallback");
    const fc = changed.find((f: any) => f.file === file).functions.find((f: any) => f.name === fn.name);
    const receiver = fn.body[2].e.receiver;
    const claim = fc.exprs.find((e: any) => e.pos[0] === receiver.pos[0] && e.pos[1] === receiver.pos[1]);
    assert.ok(claim);
    mutate(claim.type.atoms[0].fields[0]);
    for (const mode of ["--check-stateful-source", "--produce-stateful-source"]) {
      const result = run(mode, source, changed);
      assert.notEqual(result.status, 0, `${name}: ${mode} accepted the forged contract`);
    }
  }
  const context = vm.createContext({});
  vm.runInContext(stripTypes(fs.readFileSync(file, "utf8")), context, {timeout: 1000});
  for (const seed of [false, true]) {
    assert.equal(vm.runInContext(`replacedCallback(${seed})`, context, {timeout: 1000}), true);
    assert.equal(vm.runInContext(`recursiveCallback(${seed})`, context, {timeout: 1000}), seed);
  }
  console.log("  callable cells: original claims, independent checking, invariant rejection and JavaScript witnesses OK");
} finally {
  fs.rmSync(tmp, {recursive: true, force: true});
}
