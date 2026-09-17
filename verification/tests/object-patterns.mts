#!/usr/bin/env node
import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import vm from "node:vm";
import { spawnSync } from "node:child_process";
import type { Ast } from "../tools/fragment.mts";
import type { ClaimType } from "../tools/claim.mts";
import type { SourceClaims } from "../tools/source-claims.mts";
import { fileOf, functionOf, type SkjsClaims } from "../tools/skjs-claims.mts";
import { stripTypes } from "../tools/strip-types.mts";
import { at, binding, fn, must, stmt } from "./edits.mts";
// Object patterns on `const`: one statement entry, the initializer once, each
// property read in order, a default only on an undefined read, every binding
// an immutable snapshot. Both producers verify the fixture; edits to the
// source and to the claims show what the lowering commits to.

const [astPath, claimsPath, tscPath, fileKey, verifier] = process.argv.slice(2);
const ast: Ast = JSON.parse(fs.readFileSync(astPath, "utf8"));
const claims: SkjsClaims = JSON.parse(fs.readFileSync(claimsPath, "utf8"));
const tsc: SourceClaims = JSON.parse(fs.readFileSync(tscPath, "utf8"));
const source = fs.readFileSync(fileKey, "utf8");
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "object-patterns-"));
const clone = <T,>(x: T): T => JSON.parse(JSON.stringify(x));
let passed = 0;

type Kind = "stateful-source" | "source-claims";
function run(kind: Kind, a: Ast, c: unknown) {
  const ap = path.join(tmp, "ast.json"),
    cp = path.join(tmp, "claims.json"),
    ep = path.join(tmp, "evidence.json");
  fs.writeFileSync(ap, JSON.stringify(a));
  fs.writeFileSync(cp, JSON.stringify(c));
  const r = spawnSync(verifier, [`--produce-${kind}`, ap, cp, fileKey, ep, "10"], {
    encoding: "utf8",
    timeout: 60000,
  });
  if (r.error || r.signal) throw r.error || Error(String(r.signal));
  if (r.status === 0) {
    const checked = spawnSync(verifier, [`--check-${kind}`, ap, cp, fileKey, ep], {
      encoding: "utf8",
      timeout: 60000,
    });
    if (checked.status !== 0)
      throw Error(`certificate rejected: ${checked.stderr}`);
  }
  return r;
}
function expect(name: string, r: ReturnType<typeof run>, accept: boolean, message = "") {
  const output = r.stdout + r.stderr;
  if ((r.status === 0) !== accept || (message && !output.includes(message)))
    throw Error(`${name}: unexpected exit ${r.status}: ${output}`);
  passed++;
  console.log(`  ${name}: OK`);
}
/** The fixture and each producer's claims cut down to one function. */
const only = (a: Ast, name: string): Ast => ({ ...clone(a), functions: [fn(clone(a), name)] });
const skjsFor = (c: SkjsClaims, name: string): SkjsClaims => [
  { ...clone(fileOf(c, fileKey)), functions: [clone(functionOf(c, fileKey, name))] },
];
const numberLit = (v: string): ClaimType => ({ top: false, atoms: [{ a: "numberlit", v }] });
/** Where a statement's text starts within the named function. */
const startOf = (name: string, text: string): number => {
  const start = source.indexOf(text, source.indexOf(`function ${name}(`));
  assert(start >= 0, `fixture text ${JSON.stringify(text)}`);
  return start;
};

try {
  expect("both producers verify the whole fixture · SKJS", run("stateful-source", ast, claims), true);
  expect("both producers verify the whole fixture · tsc", run("source-claims", ast, tsc), true);

  // The entry after the pattern is checked on both arms of a default: the
  // read's defined slice is a number, not the default's singleton.
  const forged = skjsFor(claims, "defaultedField");
  binding(functionOf(forged, fileKey, "defaultedField"), startOf("defaultedField", "return value"), "value").type = numberLit("0");
  expect(
    "a default does not make the binding its singleton",
    run("stateful-source", only(ast, "defaultedField"), forged),
    false,
  );

  // Without the default the binding admits undefined, which the producer's
  // entry claim for a number does not.
  const undefaulted = only(ast, "defaultedField");
  must(stmt(at(undefaulted.functions[0].body, 1), "pattern").props[0], "the property").default_ = null;
  expect(
    "the default is what removes undefined from the binding",
    run("stateful-source", undefaulted, skjsFor(claims, "defaultedField")),
    false,
  );

  // A read the record contract does not name has no location.
  const unnamed = only(ast, "plainField");
  must(stmt(at(unnamed.functions[0].body, 1), "pattern").props[0], "the property").field = "other";
  expect(
    "a pattern reads only fields the contract names",
    run("stateful-source", unnamed, skjsFor(claims, "plainField")),
    false,
    "pattern reads a field 'other' the contract does not name",
  );

  // The binding is a copy: a claim that the later write reached it is refused.
  const written = skjsFor(claims, "snapshotSurvivesWrite");
  binding(functionOf(written, fileKey, "snapshotSurvivesWrite"), startOf("snapshotSurvivesWrite", "return value"), "value").type = numberLit("0");
  expect(
    "a later write to the field does not reach the binding",
    run("stateful-source", only(ast, "snapshotSurvivesWrite"), written),
    false,
  );

  // The parser admits what the lowering states, and nothing else.
  for (const [name, text, message] of [
    ["mutable pattern", "let { value } = box; return value;", "a `let` pattern is outside the fragment"],
    ["pattern beside a declarator", "const { value } = box, other = 1; return value;", "a pattern declares alone"],
    ["nested pattern", "const { value: { inner } } = box; return inner;", "nested patterns are outside the fragment"],
    ["rest element", "const { ...rest } = box; return rest.value;", "rest elements are outside the fragment"],
    ["empty pattern", "const {} = box; return 0;", "an empty pattern binds nothing"],
    [
      "pattern in a closure body",
      "const f = (): number => { const { value } = box; return value; }; return f();",
      "a pattern in a closure body is outside the fragment",
    ],
  ] as const) {
    const file = path.join(tmp, "gated.ts");
    fs.writeFileSync(file, `function gated(): number { const box = { value: 1 }; ${text} }\n`);
    const r = spawnSync(process.execPath, [path.resolve(import.meta.dirname, "../tools/fragment-parse.mts"), file], {
      encoding: "utf8",
    });
    assert.notEqual(r.status, 0, name);
    assert(r.stderr.startsWith("gate:") && r.stderr.includes(message), `${name}: ${r.stderr}`);
    passed++;
    console.log(`  ${name}: gated`);
  }

  // The source means what the claims say it means.
  const context = vm.createContext({});
  vm.runInContext(stripTypes(source), context);
  assert.equal(vm.runInContext("defaultedField(undefined)", context), 0);
  assert.equal(vm.runInContext("defaultedField(3)", context), 3);
  assert.equal(vm.runInContext("plainField(4)", context), 4);
  assert.equal(vm.runInContext("orderedDefaults(undefined)", context), 2);
  assert.equal(vm.runInContext("orderedDefaults(5)", context), 5);
  assert.equal(vm.runInContext("snapshotSurvivesWrite(7)", context), 7);
  passed++;
  console.log("  source executions agree with the verified contracts: OK");
  console.log(`Object patterns: ${passed} passed, 0 failed`);
} finally {
  fs.rmSync(tmp, { recursive: true, force: true });
}
