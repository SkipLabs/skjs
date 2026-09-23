#!/usr/bin/env node
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { spawnSync } from "node:child_process";
import { decodeClaimType, type ClaimType } from "../tools/claim.mts";
import type { Ast } from "../tools/fragment.mts";
import type { SourceClaims } from "../tools/source-claims.mts";
import { fileOf, functionOf, type SkjsClaims } from "../tools/skjs-claims.mts";
import { at, claimAt, fn, sourceType, stmt } from "./edits.mts";
// Strings in the source fragment: the family, its singletons, the one
// inclusion between them, and equality with a literal. Both producers verify
// the fixture; the edits check that nothing wider is admitted and that an
// equality test decides only what it can.

const [astPath, claimsPath, tscPath, fileKey, verifier] = process.argv.slice(2);
const ast: Ast = JSON.parse(fs.readFileSync(astPath, "utf8"));
const claims: SkjsClaims = JSON.parse(fs.readFileSync(claimsPath, "utf8"));
const tsc: SourceClaims = JSON.parse(fs.readFileSync(tscPath, "utf8"));
const source = fs.readFileSync(fileKey, "utf8");
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "strings-"));
const clone = <T,>(x: T): T => JSON.parse(JSON.stringify(x));
const string: ClaimType = { top: false, atoms: [{ a: "string" }] };
const lit = (v: string): ClaimType => ({ top: false, atoms: [{ a: "stringlit", v }] });
let passed = 0;

type Kind = "stateful-source" | "source-claims";
function run(kind: Kind, a: Ast, c: unknown) {
  const ap = path.join(tmp, "ast.json"), cp = path.join(tmp, "claims.json");
  const ep = path.join(tmp, "evidence.json");
  fs.writeFileSync(ap, JSON.stringify(a));
  fs.writeFileSync(cp, JSON.stringify(c));
  const r = spawnSync(verifier, [`--produce-${kind}`, ap, cp, fileKey, ep, "10"], { encoding: "utf8" });
  if (r.error || r.signal) throw r.error || Error(String(r.signal));
  if (r.status === 0) {
    const checked = spawnSync(verifier, [`--check-${kind}`, ap, cp, fileKey, ep], { encoding: "utf8" });
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

try {
  const exported = fileOf(claims, fileKey).functions;
  const byName = (n: string) => functionOf(claims, fileKey, n);
  for (const f of exported) { decodeClaimType(f.retType); f.params.forEach((p) => decodeClaimType(p.type)); }
  if (JSON.stringify(byName("idString").retType) !== JSON.stringify(string))
    throw Error("SKJS should export the string family");
  if (JSON.stringify(byName("singletonString").retType) !== JSON.stringify(lit("on")))
    throw Error("SKJS should preserve the string singleton, not widen it");

  expect("strings are accepted · SKJS", run("stateful-source", ast, claims), true);
  expect("strings are accepted · tsc", run("source-claims", ast, tsc), true);

  // A singleton is below the family; the family is not below the singleton.
  const widen = clone(claims);
  functionOf(widen, fileKey, "singletonString").retType = string;
  expect("the family cannot stand in for a singleton result",
    run("stateful-source", ast, widen), false, "from the source annotation");
  const narrow = clone(ast);
  fn(narrow, "idString").retType = sourceType(lit("on"));
  expect("a string result cannot be narrowed to a singleton", run("stateful-source", narrow, claims), false);

  // Distinct singletons are unrelated in both directions.
  const other = clone(claims);
  functionOf(other, fileKey, "singletonString").retType = lit("off");
  expect("a different string is a different singleton",
    run("stateful-source", ast, other), false, "from the source annotation");

  // A string is not a number, and not a Boolean.
  for (const [name, atom] of [["number", "number"], ["boolean", "boolean"]] as const) {
    const wrong = clone(claims);
    functionOf(wrong, fileKey, "idString").retType = { top: false, atoms: [{ a: atom }] };
    expect(`a string is not a ${name}`, run("stateful-source", ast, wrong), false, "from the source annotation");
  }

  // Equality decides a finite union on both arms, and nothing more: the
  // negative arm excludes the tested literal, not the other one.
  const swapped = skjsFor(claims, "discriminate");
  const second = stmt(at(fn(ast, "discriminate").body, 1), "return").e;
  claimAt(functionOf(swapped, fileKey, "discriminate"), second.pos).type = lit("a");
  expect("the negative arm excludes the tested literal, not the other",
    run("stateful-source", only(ast, "discriminate"), swapped), false);

  console.log(`Strings: ${passed} passed, 0 failed`);
} finally {
  fs.rmSync(tmp, { recursive: true, force: true });
}
