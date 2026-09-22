#!/usr/bin/env node
import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import vm from "node:vm";
import { spawnSync } from "node:child_process";
import type { Ast } from "../tools/fragment.mts";
import type { SourceClaims } from "../tools/source-claims.mts";
import { fileOf, functionOf, type SkjsClaims } from "../tools/skjs-claims.mts";
import { stripTypes } from "../tools/strip-types.mts";
import { atom, binding, claimAt, claimType, expr, fn, must, stmt } from "./edits.mts";
// Readonly views: a read capability on a field, at a sound upper bound on its
// contents, with no write permission through the view and no retyping of the
// backing invariant. Both producers verify the fixture. A write through the
// view produces an unsatisfied write obligation; a view of a mutable Boolean cell cannot claim readonly
// `true` from its current contents; a narrower bound than the invariant's is
// refused; a stronger, invariant claim for a view is accepted.

const [astPath, claimsPath, tscPath, fileKey, verifier] = process.argv.slice(2);
const ast: Ast = JSON.parse(fs.readFileSync(astPath, "utf8"));
const claims: SkjsClaims = JSON.parse(fs.readFileSync(claimsPath, "utf8"));
const tsc: SourceClaims = JSON.parse(fs.readFileSync(tscPath, "utf8"));
const source = fs.readFileSync(fileKey, "utf8");
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "readonly-views-"));
const clone = <T,>(x: T): T => JSON.parse(JSON.stringify(x));
let passed = 0;

type Kind = "stateful-source" | "source-claims";
function run(kind: Kind, a: Ast, c: unknown) {
  const ap = path.join(tmp, "ast.json"), cp = path.join(tmp, "claims.json");
  const ep = path.join(tmp, "evidence.json");
  fs.writeFileSync(ap, JSON.stringify(a));
  fs.writeFileSync(cp, JSON.stringify(c));
  const r = spawnSync(verifier, [`--produce-${kind}`, ap, cp, fileKey, ep, "10"], { encoding: "utf8", timeout: 60000 });
  if (r.error || r.signal) throw r.error || Error(String(r.signal));
  if (r.status === 0) {
    const checked = spawnSync(verifier, [`--check-${kind}`, ap, cp, fileKey, ep], { encoding: "utf8", timeout: 60000 });
    if (checked.status !== 0) throw Error(`certificate rejected: ${checked.stderr}`);
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
const only = (a: Ast, name: string): Ast => ({ ...clone(a), functions: [fn(clone(a), name)] });
const skjsFor = (c: SkjsClaims, name: string): SkjsClaims => [
  { ...clone(fileOf(c, fileKey)), functions: [clone(functionOf(c, fileKey, name))] },
];
const tscFor = (d: SourceClaims, name: string): SourceClaims => ({
  ...clone(d), functions: [clone(must(d.functions.find((f) => f.name === name), `claims for ${name}`))],
});
const startOf = (name: string, text: string): number => {
  const start = source.indexOf(text, source.indexOf(`function ${name}(`));
  assert(start >= 0, `fixture text ${JSON.stringify(text)}`);
  return start;
};
const names = ["readView", "viewOfMutable", "viewOfFlag", "satisfiesView"];

try {
  expect("SKJS verifies the whole fixture", run("stateful-source", ast, claims), true);
  for (const name of names)
    expect(`tsc verifies ${name}`, run("source-claims", only(ast, name), tscFor(tsc, name)), true);

  // The view withholds writes: `y.f = 2` in place of `x.f = 2` is refused.
  const through = only(ast, "viewOfMutable");
  const guarded = stmt(must(through.functions[0].body[0], "the guard"), "if");
  const write = expr(stmt(must(guarded.then[1], "the write statement"), "effect").e, "write");
  expr(write.receiver, "id").name = "y";
  // The receiver's claim follows the rename: it is the view's type there.
  const viewed = skjsFor(claims, "viewOfMutable");
  const at = functionOf(viewed, fileKey, "viewOfMutable");
  claimAt(at, write.receiver.pos).type = binding(at, startOf("viewOfMutable", "x.f = 2"), "y").type;
  expect("a write through the view is not established", run("stateful-source", through, viewed), false, "evidence search failed");

  // A mutable Boolean cell viewed as readonly Boolean: after the write, the
  // view cannot claim `true`, and the invariant is not retyped.
  const flagged = skjsFor(claims, "viewOfFlag");
  const view = binding(functionOf(flagged, fileKey, "viewOfFlag"), startOf("viewOfFlag", "return view.flag"), "view");
  atom(claimType(view).atoms[0], "record").fields[0].read = { top: false, atoms: [{ a: "booleanlit", v: "true" }] };
  view.type = claimType(view);
  expect("a view cannot claim readonly true from current contents",
    run("stateful-source", only(ast, "viewOfFlag"), flagged), false);

  // A bound narrower than the backing invariant is refused; a stronger,
  // invariant claim of the same field is accepted.
  const narrower = skjsFor(claims, "readView");
  const p = must(functionOf(narrower, fileKey, "readView").params.find((q) => q.name === "x"), "the parameter");
  atom(claimType(p).atoms[0], "record").fields[0].read = { top: false, atoms: [{ a: "numberlit", v: "1" }] };
  p.type = claimType(p);
  expect("a narrower view bound than the annotation is refused",
    run("stateful-source", only(ast, "readView"), narrower), false);

  const context = vm.createContext({});
  vm.runInContext(stripTypes(source), context);
  assert.equal(vm.runInContext("readView({ f: 3 })", context), 3);
  // The write through the other alias is visible through the view.
  assert.equal(vm.runInContext("viewOfMutable({ f: 1 })", context), 2);
  assert.equal(vm.runInContext("viewOfFlag({ flag: true })", context), false);
  assert.equal(vm.runInContext("satisfiesView(1)", context), 2);
  passed++;
  console.log("  source executions agree: OK");
  console.log(`Readonly views: ${passed} passed, 0 failed`);
} finally {
  fs.rmSync(tmp, { recursive: true, force: true });
}
