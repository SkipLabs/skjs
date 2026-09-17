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
import { atom, binding, claimType, fn, must } from "./edits.mts";
// Distinct locations: a private cell is fresh, so a write to it keeps a fact
// about a parameter's field; two parameters may alias, so a write through one
// forgets the other's. SKJS and TypeScript both verify the fixture. A second
// file keeps the guard's fact across such a write: TypeScript accepts it, SKJS
// rejects it, and the verifier refuses TypeScript's claim.

const [astPath, claimsPath, tscPath, fileKey, aliasedAstPath, aliasedTscPath, aliasedKey, verifier] =
  process.argv.slice(2);
const ast: Ast = JSON.parse(fs.readFileSync(astPath, "utf8"));
const claims: SkjsClaims = JSON.parse(fs.readFileSync(claimsPath, "utf8"));
const tsc: SourceClaims = JSON.parse(fs.readFileSync(tscPath, "utf8"));
const aliasedAst: Ast = JSON.parse(fs.readFileSync(aliasedAstPath, "utf8"));
const aliasedTsc: SourceClaims = JSON.parse(fs.readFileSync(aliasedTscPath, "utf8"));
const source = fs.readFileSync(fileKey, "utf8");
const aliasedSource = fs.readFileSync(aliasedKey, "utf8");
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "distinct-cells-"));
const clone = <T,>(x: T): T => JSON.parse(JSON.stringify(x));
let passed = 0;

type Kind = "stateful-source" | "source-claims";
function run(kind: Kind, a: Ast, c: unknown, key = fileKey) {
  const ap = path.join(tmp, "ast.json"), cp = path.join(tmp, "claims.json");
  const ep = path.join(tmp, "evidence.json");
  fs.writeFileSync(ap, JSON.stringify(a));
  fs.writeFileSync(cp, JSON.stringify(c));
  const r = spawnSync(verifier, [`--produce-${kind}`, ap, cp, key, ep, "10"], { encoding: "utf8", timeout: 60000 });
  if (r.error || r.signal) throw r.error || Error(String(r.signal));
  if (r.status === 0) {
    const checked = spawnSync(verifier, [`--check-${kind}`, ap, cp, key, ep], { encoding: "utf8", timeout: 60000 });
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

try {
  expect("SKJS verifies the whole fixture", run("stateful-source", ast, claims), true);
  for (const name of ["keptAcrossOwnCell", "keptAcrossLocalCell", "lostAcrossOtherParameter"])
    expect(`tsc verifies ${name}`, run("source-claims", only(ast, name), tscFor(tsc, name)), true);
  // TypeScript keeps the guard's fact across the write through the other
  // parameter; the two may be one object, so that claim is refused.
  expect("tsc's no-aliasing assumption is refused",
    run("source-claims", aliasedAst, aliasedTsc, aliasedKey), false, "incoming edge obligation");

  // Forging the same fact into SKJS's claims is refused for the same reason:
  // no distinct-location link exists between two parameters.
  const forged = skjsFor(claims, "lostAcrossOtherParameter");
  const f = functionOf(forged, fileKey, "lostAcrossOtherParameter");
  const a = binding(f, startOf("lostAcrossOtherParameter", "return a.value"), "a");
  atom(claimType(a).atoms[0], "record").fields[0].read = { top: false, atoms: [{ a: "number" }] };
  a.type = claimType(a);
  expect("a write through a possibly aliased parameter forgets the fact",
    run("stateful-source", only(ast, "lostAcrossOtherParameter"), forged), false);

  // The aliased call is the reason: through one object, the write is seen by
  // the other's read, and the rejected program returns null as a number.
  const context = vm.createContext({});
  vm.runInContext(stripTypes(source), context);
  vm.runInContext(stripTypes(aliasedSource), context);
  assert.equal(vm.runInContext("(() => { const o = { value: 6 }; return aliasedWrite(o, o); })()", context), null);
  assert.equal(vm.runInContext("keptAcrossOwnCell({ value: 3 }, 0)", context), 3);
  assert.equal(vm.runInContext("keptAcrossLocalCell({ value: 4 })", context), 4);
  const shared = vm.runInContext("(() => { const o = { value: 5 }; return lostAcrossOtherParameter(o, o); })()", context);
  assert.equal(shared, null);
  passed++;
  console.log("  source executions agree, including the aliased call: OK");
  console.log(`Distinct cells: ${passed} passed, 0 failed`);
} finally {
  fs.rmSync(tmp, { recursive: true, force: true });
}
