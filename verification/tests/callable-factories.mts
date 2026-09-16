#!/usr/bin/env node
import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import vm from "node:vm";
import { stripTypes } from "../tools/strip-types.mts";
import { spawnSync } from "node:child_process";
import type { Ast } from "../tools/fragment.mts";
import { fileOf, functionOf, type SkjsClaims } from "../tools/skjs-claims.mts";
import { atom, claimType, fn as functionIn, last, stmt } from "./edits.mts";

/** An advisory record the producer attached, which is checked before use. */
const isRecord = (v: unknown): v is Record<string, unknown> =>
  !!v && typeof v === "object";

const [ast, claims, file, verifier] = process.argv.slice(2);
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "callable-factories-"));
try {
  const source: Ast = JSON.parse(fs.readFileSync(ast, "utf8"));
  const exported: SkjsClaims = JSON.parse(fs.readFileSync(claims, "utf8"));
  const batch = fileOf(exported, file);
  const original = fs.readFileSync(file, "utf8");
  const runtime = vm.createContext({});
  vm.runInContext(stripTypes(original), runtime, {timeout: 1000});
  for (const name of ["factoryInstances", "sharedFactoryInstances"]) {
    const fn = functionIn(source, name);
    const fc = functionOf(exported, file, name);
    const expected = name === "factoryInstances" ? [false, false, true] : [false, true, false];
    assert.equal(vm.runInContext(`${name}()`, runtime, {timeout: 1000}), name === "factoryInstances");
    // Observe locals immediately before the original outer return. Calls and
    // mutations remain the source fixture's own code; only a passive observer
    // is inserted. This is a JavaScript witness, not a Lean execution proof.
    const terminal = stmt(last(fn.body), "return");
    const at = terminal.pos[0];
    assert.match(original.slice(at), /^return\b/);
    const observations: boolean[][] = [];
    const observed = vm.createContext({
      observe: (...values: boolean[]) => { observations.push(values); },
    });
    const instrumented = original.slice(0, at) + "observe(a, b, c); " + original.slice(at);
    vm.runInContext(stripTypes(instrumented), observed, {timeout: 1000});
    assert.equal(vm.runInContext(`${name}()`, observed, {timeout: 1000}), name === "factoryInstances");
    assert.deepEqual(observations, [expected]);
    console.log(`  ${name}: JavaScript observations ${expected.join(", ")} OK`);
    assert.ok(
      !(fc.unavailableTypes ?? []).some(
        (site) => isRecord(site) && site.kind === "expression",
      ),
      name,
    );
    const input = path.join(tmp, "ast");
    const claimInput = path.join(tmp, "claims");
    fs.writeFileSync(claimInput, JSON.stringify([{...batch, functions: [fc]}]));
    fs.writeFileSync(input, JSON.stringify({...source, functions: [fn]}));
    const result = spawnSync(verifier, ["--produce-stateful-source", input, claimInput, file,
      path.join(tmp, "evidence"), "10"], {encoding: "utf8"});
    if (result.error || result.signal) throw result.error || Error(String(result.signal));
    assert.equal(result.status, 0, result.stdout + result.stderr);
    const checked = spawnSync(verifier, ["--check-stateful-source", input, claimInput, file,
      path.join(tmp, "evidence")], {encoding: "utf8"});
    assert.equal(checked.status, 0, checked.stdout + checked.stderr);
    console.log(`  ${name}: original exports and independent consumer OK`);
    // A factory's result contract must describe the returned closure's behavior.
    const forged = structuredClone(fc);
    // The claim for the factory itself: a function whose own result is one.
    const outer = forged.exprs.find((site) => {
      const first = claimType(site).atoms[0];
      return (
        first?.a === "function" && first.result.atoms[0]?.a === "function"
      );
    });
    assert.ok(outer, name);
    atom(
      atom(claimType(outer).atoms[0], "function").result.atoms[0],
      "function",
    ).result = { top: false, atoms: [{ a: "booleanlit", v: "false" }] };
    fs.writeFileSync(claimInput, JSON.stringify([{...batch, functions: [forged]}]));
    for (const mode of ["--check-stateful-source", "--produce-stateful-source"]) {
      const args = [mode, input, claimInput, file, path.join(tmp, "evidence")];
      if (mode === "--produce-stateful-source") args.push("10");
      const rejected = spawnSync(verifier, args, {encoding: "utf8"});
      if (rejected.error || rejected.signal) throw rejected.error || Error(String(rejected.signal));
      assert.notEqual(rejected.status, 0, `${name}: ${mode} accepted narrowed returned closure`);
    }
    console.log(`  ${name}: returned closure cannot promise a false-only result OK`);

  }
} finally {
  fs.rmSync(tmp, {recursive: true, force: true});
}
