import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import vm from "node:vm";
import { spawnSync } from "node:child_process";
import type { SourceClaims } from "../tools/source-claims.mts";
import { decodeTerm } from "../tools/calculus.mts";
import { stripTypes } from "../tools/strip-types.mts";
import { must } from "./edits.mts";

const [
  ast,
  raw,
  tsc,
  file,
  verifier,
  boundaryAst,
  boundaryClaims,
  boundaryFile,
] = process.argv.slice(2);
const work = fs.mkdtempSync(os.tmpdir() + "/numeric-comparisons-");
const proof = work + "/proof";
const source = fs.readFileSync(file, "utf8");
function run(mode: string, claims: string) {
  const args = [mode, ast, claims, file, proof];
  if (mode.startsWith("--produce")) args.push("10");
  const r = spawnSync(verifier, args, { encoding: "utf8", timeout: 30000 });
  assert(!r.error && !r.signal, String(r.error || r.signal));
  return r;
}
try {
  for (const [kind, claims] of [
    ["stateful-source", raw],
    ["source-claims", tsc],
  ]) {
    for (const action of ["produce", "check"]) {
      const r = run(`--${action}-${kind}`, claims);
      assert.equal(r.status, 0, r.stdout + r.stderr);
    }
  }
  const original = fs.readFileSync(proof);
  const claims: SourceClaims = JSON.parse(fs.readFileSync(tsc, "utf8"));
  const one = claims.types.findIndex((row) =>
    row.some(
      (c) =>
        typeof c === "object" &&
        "numLit" in c &&
        c.numLit.bits === "4607182418800017408",
    ),
  );
  assert(one >= 0, "the fixture declares the numeric singleton 1");
  const number = claims.types.push(["num"]) - 1;
  for (const [name, spelling] of [
    ["namedZero", "zero"],
    ["comparisonEffects", "clear()"],
  ]) {
    for (const wrongType of [[one], [number]]) {
      const changed = structuredClone(claims);
      const fn = must(
        changed.functions.find((f) => f.name === name),
        name,
      );
      const operand = must(
        fn.expressions.find((e) => source.slice(...e.pos) === spelling),
        spelling,
      );
      operand.type = wrongType;
      const input = work + "/changed";
      fs.writeFileSync(input, JSON.stringify(changed));
      for (const action of ["produce", "check"]) {
        fs.writeFileSync(proof, original);
        const r = run(`--${action}-source-claims`, input);
        assert.notEqual(r.status, 0, `${name}: forged singleton accepted`);
        if (wrongType[0] === number)
          assert.match(
            r.stderr + r.stdout,
            /equality requires a null, undefined or numeric singleton operand/,
          );
      }
    }
  }
  const test = { test: { k: { numEq: { bits: "0" } }, a: { var: { i: 0 } } } };
  assert.deepEqual(decodeTerm(test), test);
  assert.throws(() =>
    decodeTerm({
      test: { ...test.test, k: { numEq: { bits: "18446744073709551616" } } },
    }),
  );
  const broad: SourceClaims = JSON.parse(
    fs.readFileSync(boundaryClaims, "utf8"),
  );
  const broadSource = fs.readFileSync(boundaryFile, "utf8");
  const narrowed = must(
    broad.functions[0].expressions.find(
      (e) =>
        broadSource.slice(...e.pos) === "value" &&
        broadSource.slice(e.pos[0] - 7, e.pos[0]) === "return ",
    ),
    "narrowed return",
  );
  const zero = broad.types.findIndex((row) =>
    row.some(
      (c) => typeof c === "object" && "numLit" in c && c.numLit.bits === "0",
    ),
  );
  const negativeZero = broad.types.findIndex((row) =>
    row.some(
      (c) =>
        typeof c === "object" &&
        "numLit" in c &&
        c.numLit.bits === "9223372036854775808",
    ),
  );
  assert(negativeZero >= 0);
  assert.deepEqual(
    narrowed.type,
    [zero, negativeZero],
    "a zero guard includes both runtime zeros",
  );
  const limited = spawnSync(
    verifier,
    [
      "--produce-source-claims",
      boundaryAst,
      boundaryClaims,
      boundaryFile,
      work + "/boundary.proof",
      "10",
    ],
    { encoding: "utf8", timeout: 30000 },
  );
  assert(
    !limited.error && !limited.signal,
    String(limited.error || limited.signal),
  );
  assert.notEqual(
    limited.status,
    0,
    "broad numeric comparisons remain a documented proof boundary",
  );
  assert.match(
    limited.stderr,
    /evidence search failed/,
  );
  const context = vm.createContext({});
  vm.runInContext(stripTypes(source), context);
  for (const seed of [0, 1]) {
    assert.equal(vm.runInContext(`namedZero(${seed}, 0)`, context), 1);
    assert.equal(
      vm.runInContext(`numericClosure(${seed})()`, context),
      seed === 1,
    );
    assert.equal(
      vm.runInContext(`comparisonEffects(${seed}, 0)`, context),
      seed !== 0,
    );
  }
  console.log(
    "Numeric singleton comparisons: both producers, independent consumption, forged operands and source evaluation order passed",
  );
} finally {
  fs.rmSync(work, { recursive: true, force: true });
}
