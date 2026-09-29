#!/usr/bin/env node
/*
 * Variadic calls. An array rest collects every actual past the fixed ones into
 * a fresh array, and a spread passes an array's elements among the actuals,
 * read where it is written. Invocation of variadic code binds the fixed
 * actuals and yields the term that allocates the array; a spread is read by
 * the call once every earlier actual is a value.
 */
import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import vm from "node:vm";
import { spawnSync } from "node:child_process";
import { stripTypes } from "../tools/strip-types.mts";
import type { SourceClaims } from "../tools/source-claims.mts";
import type { Arrow } from "../tools/type-graph.mts";
import { fileOf, type SkjsClaims } from "../tools/skjs-claims.mts";

const [
  astPath,
  claimsPath,
  file,
  verifier,
  tscPath,
  holesFile,
  orderFile,
  copyFile,
] = process.argv.slice(2);
const work = fs.mkdtempSync(path.join(os.tmpdir(), "variadic-arguments-"));
let passed = 0;
try {
  const source = fs.readFileSync(file, "utf8");
  const execute = (text: string, expression: string) => {
    const context = vm.createContext({});
    vm.runInContext(stripTypes(text), context, { timeout: 1000 });
    return vm.runInContext(expression, context, { timeout: 1000 });
  };
  for (const seed of [false, true]) {
    const s = String(seed);
    assert.equal(
      execute(source, `JSON.stringify(returnsRest(${s}, ${!seed}, ${s}))`),
      JSON.stringify([!seed, seed]),
    );
    assert.equal(
      execute(source, `JSON.stringify(callsCollector(${s}))`),
      JSON.stringify([seed, !seed]),
    );
    assert.equal(
      execute(source, `JSON.stringify(spreadsIntoRest(${s}))`),
      JSON.stringify([seed, seed, seed, seed, seed]),
    );
    assert.equal(
      execute(source, `JSON.stringify(spreadsTupleIntoRest(${s}))`),
      JSON.stringify([seed, seed]),
    );
    assert.equal(execute(source, `passesCollectorOn(${s})`), seed);
    // A variadic value called through a fixed signature, an omitted optional
    // parameter before the rest, one value with fixed and variadic
    // signatures, and a variadic callable object with a field.
    assert.equal(
      execute(source, `JSON.stringify(variadicAsFixed(${s}))`),
      JSON.stringify([seed]),
    );
    assert.equal(execute(source, `omitsBeforeRest(${s})`), undefined);
    assert.equal(
      execute(source, `JSON.stringify(mixedSignatures(${s}))`),
      JSON.stringify([seed, seed]),
    );
    assert.equal(
      execute(source, `JSON.stringify(variadicCallableField(${s}))`),
      JSON.stringify([!seed, seed]),
    );
  }
  // Each call collects its own array, including an empty one.
  assert.equal(
    execute(source, "returnsRest(true) !== returnsRest(true)"),
    true,
  );
  assert.equal(execute(source, "returnsRest(true).length"), 0);
  passed++;
  console.log("  collected and spread arguments at run time: OK");

  // A spread passes `undefined` at a hole, and the rest then holds it: a
  // `T[]` rest cannot collect a spread of a `T[]` that may have holes.
  const holeWitnesses: [string, string][] = [
    [holesFile, "spreadsArrayIntoRest"],
    ["verification/ocaml-producer/examples/spread-holes.ts", "spreadsArray"],
  ];
  for (const [file, fn] of holeWitnesses) {
    const text = fs.readFileSync(file, "utf8");
    for (const seed of [false, true]) {
      assert.equal(execute(text, `${fn}(${seed})[1]`), undefined);
      assert.equal(execute(text, `1 in ${fn}(${seed})`), true);
      assert.equal(execute(text, `${fn}(${seed}).length`), 3);
    }
  }
  // A spread is read where it is written: an actual after it that writes the
  // array does not change what the spread passed.
  const order = `const collect = (...rest) => rest; const values = [1];`;
  assert.equal(
    execute(order, "JSON.stringify(collect(...values, (values[0] = 2, 3)))"),
    "[1,3]",
  );
  passed++;
  console.log("  a spread passes undefined at a hole, read where written: OK");

  const tsc: SourceClaims<number> = JSON.parse(fs.readFileSync(tscPath, "utf8"));
  const astText = fs.readFileSync(astPath, "utf8");
  const input = path.join(work, "ast"),
    contract = path.join(work, "claims"),
    evidence = path.join(work, "evidence");
  const check = (mode: string, ast: string, c: SourceClaims<number>, key = file) => {
    fs.writeFileSync(input, ast);
    fs.writeFileSync(contract, JSON.stringify(c));
    const args = [mode, input, contract, key, evidence];
    if (mode === "--produce-source-claims") args.push("10");
    const r = spawnSync(verifier, args, { encoding: "utf8" });
    if (r.error || r.signal) throw r.error || Error(String(r.signal));
    return r;
  };
  for (const mode of ["--produce-source-claims", "--check-source-claims"]) {
    const r = check(mode, astText, tsc);
    assert.equal(r.status, 0, `TypeScript ${mode}: ${r.stdout}${r.stderr}`);
  }
  passed++;
  console.log("  TypeScript's claims verify: OK");

  // What a variadic signature says is checked, never assumed: narrow the
  // element type of a rest, or state a fixed arrow in its place, and the
  // same program fails.
  const restRows = (c: SourceClaims<number>) =>
    c.types.flatMap((row) =>
      row.flatMap((clause) =>
        typeof clause !== "string" && "arrs" in clause && clause.arrs.variadic
          ? [clause.arrs]
          : [],
      ),
    );
  const mutations: [string, (c: SourceClaims<number>) => void][] = [
    [
      "a narrowed rest element",
      (c) => {
        for (const arrs of restRows(c))
          for (const sig of arrs.variadic ?? []) sig.arguments[1] = [1];
      },
    ],
    [
      "a fixed arrow stated for a variadic one",
      (c) => {
        for (const arrs of restRows(c)) {
          arrs.arrows.push(
            ...(arrs.variadic ?? []).map(
              (s): Arrow => ({...s, arguments: s.arguments[0]}),
            ),
          );
          delete arrs.variadic;
        }
      },
    ],
  ];
  assert.ok(restRows(tsc).length > 0, "the claims state variadic signatures");
  for (const [name, edit] of mutations) {
    const c = structuredClone(tsc);
    edit(c);
    for (const mode of ["--check-source-claims", "--produce-source-claims"])
      assert.notEqual(check(mode, astText, c).status, 0, name);
    passed++;
    console.log(`  ${name}: OK`);
  }

  const parseAndClaim = (source: string, name: string) => {
    const ast = spawnSync(
      "node",
      ["verification/tools/fragment-parse.mts", source],
      { encoding: "utf8" },
    );
    assert.equal(ast.status, 0, ast.stderr);
    const out = path.join(work, `${name}.tsc`);
    const claims = spawnSync(
      "node",
      ["verification/tools/tsc-claims.mts", source, "--out", out],
      { encoding: "utf8" },
    );
    assert.equal(claims.status, 0, claims.stderr);
    const accepted: unknown = JSON.parse(
      fs.readFileSync(out + ".outcomes.json", "utf8"),
    );
    for (const [file, fn] of holeWitnesses)
      if (file === source)
        assert.deepEqual(accepted, { [fn]: true }, "TypeScript accepts the unsound witness");
    const c: SourceClaims<number> = JSON.parse(fs.readFileSync(out, "utf8"));
    return { ast: ast.stdout, claims: c };
  };

  // Check the viewer witness too, so its source cannot silently diverge from
  // the TypeScript acceptance and runtime counterexample checked above.
  parseAndClaim(holeWitnesses[1][0], "viewer-holes");

  // A spread is read where it is written, even when a later actual writes the
  // same array: the call spreads a copy made at the spread.
  const orderSource = fs.readFileSync(orderFile, "utf8");
  for (const seed of [false, true])
    assert.equal(
      execute(orderSource, `JSON.stringify(readsBeforeLaterWrite(${seed}))`),
      JSON.stringify([seed, !seed]),
    );
  {
    const { ast, claims } = parseAndClaim(orderFile, "order");
    for (const mode of ["--produce-source-claims", "--check-source-claims"]) {
      const r = check(mode, ast, claims, orderFile);
      assert.equal(r.status, 0, `order ${mode}: ${r.stdout}${r.stderr}`);
    }
  }
  passed++;
  console.log("  a spread before a later write reads the array first: OK");

  // Copying a known dense tuple preserves its contract across a later effect.
  {
    const text = fs.readFileSync(copyFile, "utf8");
    for (const seed of [false, true])
      assert.equal(execute(text, `JSON.stringify(copiesIntoStrictRest(${seed}))`),
        JSON.stringify([seed, seed, !seed]));
    const { ast, claims } = parseAndClaim(copyFile, "copy");
    for (const mode of ["--produce-source-claims", "--check-source-claims"]) {
      const r = check(mode, ast, claims, copyFile);
      assert.equal(r.status, 0, `dense copy ${mode}: ${r.stdout}${r.stderr}`);
    }
  }
  passed++;
  console.log("  a dense spread copy into a Boolean rest: OK");

  // A genuinely sparse array still cannot supply a Boolean rest.
  const refusals: [string, string, RegExp][] = [
    [holesFile, "holes", /may have holes passes `undefined`/],
  ];
  for (const [negative, name, reason] of refusals) {
    const { ast, claims } = parseAndClaim(negative, name);
    for (const mode of ["--produce-source-claims", "--check-source-claims"]) {
      const r = check(mode, ast, claims, negative);
      assert.notEqual(r.status, 0, `${name} ${mode}: expected a refusal`);
      assert.match(r.stdout + r.stderr, reason, name);
    }
    passed++;
    console.log(`  refused, ${name}: OK`);
  }

  // SKJS reads a rest parameter as a readonly array and rejects these
  // functions; where it cannot state a variadic signature it says so by name.
  const skjs: SkjsClaims = JSON.parse(fs.readFileSync(claimsPath, "utf8"));
  assert.ok(
    fileOf(skjs, file).functions.some((f) =>
      (f.unavailableTypes ?? []).some(
        (u) =>
          typeof u === "object" &&
          u !== null &&
          "reason" in u &&
          u.reason === "function-rest-parameter",
      ),
    ),
    "SKJS names the variadic signatures it cannot export",
  );
  passed++;
  console.log("  SKJS names its variadic gap: OK");
  console.log(`Variadic arguments: ${passed} passed, 0 failed`);
} finally {
  fs.rmSync(work, { recursive: true, force: true });
}
