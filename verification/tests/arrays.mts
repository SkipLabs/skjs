#!/usr/bin/env node
import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import vm from "node:vm";
import { spawnSync } from "node:child_process";
import surface from "../tools/claim-text.mts";
import { decodeGraph } from "../tools/type-graph.mts";
import type { Ast } from "../tools/fragment.mts";
import type { SourceClaims } from "../tools/source-claims.mts";
import { fileOf, functionOf, type SkjsClaims } from "../tools/skjs-claims.mts";
import { stripTypes } from "../tools/strip-types.mts";
import { fn, must } from "./edits.mts";
// Arrays share their backing store across aliases. Readonly element contracts
// are covariant read capabilities; writes remain invariant. Source reads need
// valid index singletons, and destructuring needs a fresh literal: a type does
// not establish an external iterator's behavior or effects. The editor must
// round-trip every supported array and store contract without losing readonly.

const [astPath, claimsPath, tscPath, fileKey, verifier] = process.argv.slice(2);
const ast: Ast = JSON.parse(fs.readFileSync(astPath, "utf8"));
const claims: SkjsClaims = JSON.parse(fs.readFileSync(claimsPath, "utf8"));
const tsc: SourceClaims = JSON.parse(fs.readFileSync(tscPath, "utf8"));
const source = fs.readFileSync(fileKey, "utf8");
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "arrays-"));
const clone = <T,>(x: T): T => JSON.parse(JSON.stringify(x));
let passed = 0;

type Kind = "stateful-source" | "source-claims";
function run(kind: Kind, a: Ast, c: unknown) {
  const ap = path.join(tmp, "ast.json"),
    cp = path.join(tmp, "claims.json");
  const ep = path.join(tmp, "evidence.json");
  fs.writeFileSync(ap, JSON.stringify(a));
  fs.writeFileSync(cp, JSON.stringify(c));
  const r = spawnSync(
    verifier,
    [`--produce-${kind}`, ap, cp, fileKey, ep, "10"],
    { encoding: "utf8", timeout: 120000 },
  );
  if (r.error || r.signal) throw r.error || Error(String(r.signal));
  if (r.status === 0) {
    const checked = spawnSync(
      verifier,
      [`--check-${kind}`, ap, cp, fileKey, ep],
      { encoding: "utf8", timeout: 120000 },
    );
    if (checked.status !== 0)
      throw Error(`certificate rejected: ${checked.stderr}`);
  }
  return r;
}
function expect(
  name: string,
  r: ReturnType<typeof run>,
  accept: boolean,
  message = "",
) {
  const output = r.stdout + r.stderr;
  if ((r.status === 0) !== accept || (message && !output.includes(message)))
    throw Error(`${name}: unexpected exit ${r.status}: ${output}`);
  passed++;
  console.log(`  ${name}: OK`);
}
const only = (a: Ast, name: string): Ast => ({
  ...clone(a),
  functions: [fn(clone(a), name)],
});
const skjsFor = (c: SkjsClaims, name: string): SkjsClaims => [
  {
    ...clone(fileOf(c, fileKey)),
    functions: [clone(functionOf(c, fileKey, name))],
  },
];
const tscFor = (d: SourceClaims, name: string): SourceClaims => ({
  ...clone(d),
  functions: [
    clone(
      must(
        d.functions.find((f) => f.name === name),
        `claims for ${name}`,
      ),
    ),
  ],
});
const startOf = (name: string, text: string): number => {
  const start = source.indexOf(text, source.indexOf(`function ${name}(`));
  assert(start >= 0, `fixture text ${JSON.stringify(text)}`);
  return start;
};
/** Every array atom in a producer's claims, made readonly where it is. */
function readonlyArrays(value: unknown): void {
  if (Array.isArray(value)) value.forEach(readonlyArrays);
  else if (value && typeof value === "object") {
    if ("a" in value && value.a === "array")
      Object.assign(value, { readonly: true });
    Object.values(value).forEach(readonlyArrays);
  }
}
const sound = [
  "tupleFirst",
  "unionTuple",
  "lengthOf",
  "readonlyCovariant",
  "readonlyTupleCovariant",
  "freshPattern",
  "aliasGrowth",
];
const gated = [
  "declaredPrefix",
  "inferredDefault",
  "assignedPrefix",
  "assignedDefault",
  "indexed",
  "negativeKey",
  "fractionalKey",
];
const unchecked = ["literalRead", "writeElem", "readonlyArr"];

try {
  for (const name of [...sound, ...unchecked])
    expect(
      `SKJS verifies ${name}`,
      run("stateful-source", only(ast, name), skjsFor(claims, name)),
      true,
    );
  for (const name of gated) {
    const reason = ["indexed", "negativeKey", "fractionalKey"].includes(name)
      ? "numeric"
      : "external iterators";
    expect(
      `SKJS boundary for ${name}`,
      run("stateful-source", only(ast, name), skjsFor(claims, name)),
      false,
      reason,
    );
    expect(
      `TS boundary for ${name}`,
      run("source-claims", only(ast, name), tscFor(tsc, name)),
      false,
      reason,
    );
  }
  for (const name of sound)
    expect(
      `tsc verifies ${name}`,
      run("source-claims", only(ast, name), tscFor(tsc, name)),
      true,
    );
  // tsc claims the element type for an index read that may be out of range
  // or a hole; the read is typed with `undefined` and the claim is refused.
  for (const name of unchecked)
    expect(
      `tsc's unchecked index read in ${name} is refused`,
      run("source-claims", only(ast, name), tscFor(tsc, name)),
      false,
      "source expression obligation",
    );

  const writable = skjsFor(claims, "readonlyCovariant");
  const makeWritable = (v: unknown): void => {
    if (Array.isArray(v)) v.forEach(makeWritable);
    else if (v && typeof v === "object") {
      if ("a" in v && v.a === "array") Object.assign(v, { readonly: false });
      Object.values(v).forEach(makeWritable);
    }
  };
  makeWritable(writable);
  expect(
    "writable array widening is refused",
    run("stateful-source", only(ast, "readonlyCovariant"), writable),
    false,
  );

  for (const text of [
    "number[]",
    "Array<unknown>",
    "{ value: never = (number) }",
    "readonly (number | string)[]",
    "[number, string?, ...Array<boolean>]",
    "Store<ReadonlyArray<number>>",
  ]) {
    const type = surface.parseType(text);
    const printed = surface.printType(type);
    assert.equal(printed.printable, true);
    assert.deepEqual(surface.parseType(printed.text), type);
    const graph = clone(tsc.types);
    const lowered = surface.lower(graph, type);
    decodeGraph(graph);
    const restored = surface.printType(surface.lift(graph, lowered.type));
    assert.equal(restored.printable, true);
    assert.deepEqual(surface.parseType(restored.text), type);
  }
  assert.throws(() => surface.parseType("[number?, string]"));
  assert.throws(() => surface.parseType("[...Array<number>, string]"));
  const missingFlag = clone(tsc.types);
  for (const row of missingFlag)
    for (const clause of row)
      if (typeof clause === "object" && "list" in clause)
        Reflect.deleteProperty(clause.list.first, "readonly");
  assert.throws(() => decodeGraph(missingFlag));

  // The same write through a readonly array: the store is a view, and the
  // write-back has no permission.
  const viewed = skjsFor(claims, "writeElem");
  readonlyArrays(viewed);
  expect(
    "a write through a readonly array is refused",
    run("stateful-source", only(ast, "writeElem"), viewed),
    false,
  );

  const context = vm.createContext({});
  vm.runInContext(stripTypes(source), context);
  assert.equal(vm.runInContext("literalRead(3)", context), 3);
  assert.equal(vm.runInContext("freshPattern(9)", context), 9);
  assert.equal(vm.runInContext("aliasGrowth([])", context), 4);
  // These admitted JS inputs explain why a plain type cannot justify the
  // old direct-index replacement for an external iterator or numeric key.
  assert.equal(
    vm.runInContext(
      "const unusual = [1]; unusual[-1] = 7; negativeKey(unusual)",
      context,
    ),
    7,
  );
  assert.equal(
    vm.runInContext(
      "const fraction = [1]; fraction[0.5] = 9; fractionalKey(fraction)",
      context,
    ),
    9,
  );
  assert.equal(
    vm.runInContext(
      "const custom = [1]; custom[Symbol.iterator] = function*(){yield 7}; inferredDefault(custom)",
      context,
    ),
    7,
  );
  assert.equal(vm.runInContext('tupleFirst([1, "a"])', context), 1);
  assert.equal(vm.runInContext("unionTuple([2])", context), 2);
  assert.equal(vm.runInContext("indexed([1, 2], 1)", context), 2);
  assert.equal(vm.runInContext("indexed([1], 5)", context), undefined);
  assert.equal(vm.runInContext("lengthOf([1, 2, 3])", context), 3);
  assert.equal(vm.runInContext("writeElem([1])", context), 5);
  assert.equal(vm.runInContext("readonlyArr([7])", context), 7);
  assert.equal(vm.runInContext('declaredPrefix([1, "x"])', context), "x");
  assert.equal(vm.runInContext('declaredPrefix([0, "x"])', context), "");
  assert.equal(vm.runInContext("inferredDefault([])", context), 0);
  assert.equal(vm.runInContext("inferredDefault([4])", context), 4);
  assert.equal(vm.runInContext("assignedPrefix([1, 2])", context), 3);
  assert.equal(vm.runInContext("assignedDefault([])", context), 0);
  assert.equal(vm.runInContext("assignedDefault([7])", context), 7);
  passed++;
  console.log("  source executions agree: OK");
  console.log(`Arrays: ${passed} passed, 0 failed`);
} finally {
  fs.rmSync(tmp, { recursive: true, force: true });
}
