#!/usr/bin/env node
/*
 * Arguments that are not written one by one. A rest parameter collects the
 * arguments after the fixed ones into a fresh array; a spread writes the
 * elements of one array in place of the last arguments. Both are a fixed
 * number of positions, fixed by a tuple contract, so the signature says how
 * many and invocation binds what it is given: nothing here needs a variadic
 * invocation rule, and an unbounded `T[]` rest stays refused at the gate.
 */
import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import vm from "node:vm";
import { spawnSync } from "node:child_process";
import { stripTypes } from "../tools/strip-types.mts";
import type { Ast } from "../tools/fragment.mts";
import type { SourceClaims } from "../tools/source-claims.mts";
import { fileOf, type SkjsClaims } from "../tools/skjs-claims.mts";
import { must } from "./edits.mts";

const [astPath, claimsPath, file, verifier, tscPath] = process.argv.slice(2);
const work = fs.mkdtempSync(path.join(os.tmpdir(), "rest-arguments-"));
let passed = 0;
try {
  const source = fs.readFileSync(file, "utf8");
  const execute = (text: string, expression: string) => {
    const context = vm.createContext({});
    vm.runInContext(stripTypes(text), context, { timeout: 1000 });
    return vm.runInContext(expression, context, { timeout: 1000 });
  };
  for (const seed of [false, true]) {
    assert.equal(execute(source, `collectsRest(${seed}, ${!seed}, ${seed})`), !seed);
    assert.equal(execute(source, `readsLaterElement(${seed}, ${seed}, null)`), null);
    assert.equal(execute(source, `spreadsPair(${seed})`), seed);
    assert.equal(execute(source, `spreadsAfterFixed(${seed})`), seed);
  }
  // Each call collects its own array: a rest parameter is an allocation, not a
  // view of the caller's arguments.
  const collects = `function collect(first, ...rest) { return rest; }`;
  assert.equal(execute(collects, "JSON.stringify(collect(1, 2, 3))"), "[2,3]");
  assert.equal(execute(collects, "collect(1, 2) !== collect(1, 2)"), true);
  passed++;
  console.log("  collected and spread arguments at run time: OK");

  // A spread reads its elements where it is written, after every earlier
  // argument has run. The fragment has no array write inside a closure, so
  // this order is witnessed here rather than certified.
  const ordered = `function order(seed) {
  const pair = [seed, seed];
  const replace = (value) => { pair[0] = value; return value; };
  const pick = (first, second, third) => second;
  return pick(replace(!seed), ...pair);
}`;
  for (const seed of [false, true])
    assert.equal(execute(ordered, `order(${seed})`), !seed,
      "a spread reads its elements after the arguments written before it");
  passed++;
  console.log("  a spread reads its elements after earlier arguments: OK");

  const ast: Ast = JSON.parse(fs.readFileSync(astPath, "utf8"));
  const skjs: SkjsClaims = JSON.parse(fs.readFileSync(claimsPath, "utf8"));
  const tsc: SourceClaims = JSON.parse(fs.readFileSync(tscPath, "utf8"));
  const input = path.join(work, "ast"),
    contract = path.join(work, "claims"),
    evidence = path.join(work, "evidence");
  const check = (mode: string, a: Ast, c: SkjsClaims | SourceClaims) => {
    fs.writeFileSync(input, JSON.stringify(a));
    fs.writeFileSync(contract, JSON.stringify(c));
    const command = Array.isArray(c) ? mode : mode.replace("stateful-source", "source-claims");
    const args = [command, input, contract, file, evidence];
    if (mode === "--produce-stateful-source") args.push("10");
    const r = spawnSync(verifier, args, { encoding: "utf8" });
    if (r.error || r.signal) throw r.error || Error(String(r.signal));
    return r;
  };
  const producers: [string, SkjsClaims | SourceClaims][] = [
    ["SKJS", skjs],
    ["TypeScript", tsc],
  ];
  for (const [name, claims] of producers)
    for (const mode of ["--produce-stateful-source", "--check-stateful-source"]) {
      const r = check(mode, ast, claims);
      assert.equal(r.status, 0, `${name} ${mode}: ${r.stdout}${r.stderr}`);
    }
  passed++;
  console.log("  both producers' claims verify independently: OK");

  /** The tuple contract a claimed type names, in the TypeScript document. */
  const tupleRow = (c: SourceClaims, label: number) => {
    const row = must(c.types[label], "a type row");
    const clause = must(row[0], "a clause");
    if (typeof clause === "string" || !("list" in clause))
      throw Error("expected a store contract");
    return clause.list.first;
  };
  const storeLabels = (c: SourceClaims) =>
    c.types.flatMap((row, label) =>
      row.some((clause) => typeof clause !== "string" && "list" in clause)
        ? [label]
        : [],
    );
  // The positions a rest or a spread stands for are the required elements of
  // its tuple contract. Change what that contract says and the same call must
  // fail: the count and the element types are checked, never assumed.
  const mutations: [string, (c: SourceClaims) => void][] = [
    [
      "a dropped tuple position",
      (c: SourceClaims) => {
        for (const label of storeLabels(c)) tupleRow(c, label).required.pop();
      },
    ],
    [
      "a retyped tuple position",
      (c: SourceClaims) => {
        for (const label of storeLabels(c)) {
          const required = tupleRow(c, label).required;
          if (required.length) required[0] = [0];
        }
      },
    ],
  ];
  for (const [name, edit] of mutations) {
    const c = structuredClone(tsc);
    edit(c);
    for (const mode of ["--check-stateful-source", "--produce-stateful-source"])
      assert.notEqual(check(mode, ast, c).status, 0, name);
    passed++;
    console.log(`  ${name}: OK`);
  }

  // SKJS types and exports these: the row is shared, not a producer gap.
  assert.equal(
    fileOf(skjs, file).functions.filter((f) =>
      (f.unavailableTypes ?? []).some(
        (u) => typeof u === "object" && u !== null && "reason" in u && u.reason === "function-rest-parameter",
      ),
    ).length,
    0,
    "SKJS is expected to export these signatures",
  );
  passed++;
  console.log("  SKJS exports a tuple rest signature: OK");
  console.log(`Rest and spread arguments: ${passed} passed, 0 failed`);
} finally {
  fs.rmSync(work, { recursive: true, force: true });
}
