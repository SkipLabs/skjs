#!/usr/bin/env node
import fs from "node:fs";
import assert from "node:assert/strict";
import { produce as tscProduce, close as closeTsc } from "../tools/tsc-claims.mts";
import os from "node:os";
import path from "node:path";
import { spawnSync } from "node:child_process";
import { fromSkjs, verifySkjs } from "../tools/annotate-source.mts";
import { decodeClaimType, type ClaimType } from "../tools/claim.mts";
import type { Ast, FunctionAst } from "../tools/fragment.mts";
import {
  fileOf,
  functionOf,
  type SkjsClaims,
  type SkjsFunction,
} from "../tools/skjs-claims.mts";
import {
  expr as exprOf,
  fn as functionIn,
  must,
  at as nth,
  sole,
  stmt,
} from "./edits.mts";
// Source extraction of generic bodies that copy T through const and fst.

const [astPath, claimsPath, fileKey, verifier] = process.argv.slice(2);
const ast: Ast = JSON.parse(fs.readFileSync(astPath, "utf8"));
const rawClaims: SkjsClaims = JSON.parse(fs.readFileSync(claimsPath, "utf8"));
const claims = structuredClone(rawClaims);
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "generic-bodies-"));
const clone = <T,>(x: T): T => JSON.parse(JSON.stringify(x));
const t: ClaimType = { top: false, atoms: [{ a: "param", name: "T" }] };
let passed = 0;
function run(a: Ast, c: SkjsClaims) {
  const ap = path.join(tmp, "ast.json");
  const cp = path.join(tmp, "claims.json");
  const ep = path.join(tmp, "evidence.json");
  fs.writeFileSync(ap, JSON.stringify(a));
  fs.writeFileSync(cp, JSON.stringify(c));
  const r = spawnSync(verifier, ["--produce-stateful-source", ap, cp, fileKey, ep, "8"], {
    encoding: "utf8",
  });
  if (r.error || r.signal) throw r.error || Error(String(r.signal));
  if (r.status === 0) {
    const checked = spawnSync(verifier, ["--check-stateful-source", ap, cp, fileKey, ep], {
      encoding: "utf8",
    });
    const output = checked.stdout + checked.stderr;
    if (checked.status !== 0)
      throw Error(`unexpected final certification result: ${output}`);
  }
  return r;
}
function expect(name: string, r: ReturnType<typeof run>, accept: boolean, message = "") {
  const output = r.stdout + r.stderr;
  if ((r.status === 0) !== accept || (message && !output.includes(message))) {
    throw Error(`${name}: unexpected exit ${r.status}: ${output}`);
  }
  passed++;
  console.log(`  ${name}: OK`);
}
try {
  const bind = functionIn(ast, "bind");
  const fst = functionIn(ast, "fst");
  const bound = sole(stmt(nth(bind.body, 0), "const"));
  decodeClaimType(must(bind.params[0], "a parameter").type);
  decodeClaimType(must(bound.annot, "the binding's annotation"));
  if (JSON.stringify(bound.annot) !== JSON.stringify(t))
    throw Error("bind const should be annotated T");
  if (fst.params.length !== 2) throw Error("fst should have two parameters");
  const exported = fileOf(claims, fileKey).functions;
  const bindC = functionOf(claims, fileKey, "bind");
  const fstC = functionOf(claims, fileKey, "fst");
  decodeClaimType(must(bindC.params[0], "a parameter").type);
  decodeClaimType(must(fstC.params[1], "a parameter").type);
  if (JSON.stringify(bindC.retType) !== JSON.stringify(t))
    throw Error("SKJS should export bind result as param T");
  const independentAst = clone(ast);
  independentAst.functions = independentAst.functions.filter((f) => f.name === "second");
  const independentClaims = clone(rawClaims).filter((f) => f.file === fileKey);
  const independentFile = must(independentClaims[0], "the claim file");
  independentFile.functions = independentFile.functions.filter((f) => f.name === "second");
  expect("distinct parameters pass direct validation from unedited SKJS claims", run(independentAst, independentClaims), true);
  for (const [name, parameter] of [["upper", "U"], ["boundChain", "V"]]) {
    const f = functionOf(claims, fileKey, name);
    const expected = { top: false, atoms: [{ a: "param", name: parameter }] };
    if (JSON.stringify(must(f.params[0], "a parameter").type) !== JSON.stringify(expected))
      throw Error(`${name}: SKJS must preserve dependent parameter ${parameter}`);
  }
  expect("dependent bounds pass direct validation from unedited SKJS claims", run(ast, rawClaims), true);
  const noAnnot = clone(ast);
  sole(stmt(nth(functionIn(noAnnot, "bind").body, 0), "const")).annot = null;
  expect("generic const infers the rigid initializer type", run(noAnnot, claims), true);
  const badInit = clone(ast);
  sole(stmt(nth(functionIn(badInit, "bind").body, 0), "const")).init = {
    k: "lit",
    pos: bound.init.pos,
    lit: { a: "booleanlit", v: "true" },
  };
  expect("const cannot be initialized from true", run(badInit, claims), false, "cannot establish true ≤ T");
  const fstTrue = clone(ast);
  stmt(nth(functionIn(fstTrue, "fst").body, 0), "return").e = {
    k: "lit",
    pos: stmt(nth(fst.body, 0), "return").e.pos,
    lit: { a: "booleanlit", v: "true" },
  };
  expect("fst returning true is not a T-copy", run(fstTrue, claims), false, "cannot establish true ≤ T");
  // These mutations leave producer claims alone: source obligations must reject
  // reverse bounds and parameter conflation even with plausible signatures.
  const mutate = (name: string, edit: (f: FunctionAst) => void) => {
    const a = clone(ast);
    edit(functionIn(a, name));
    return run(a, claims);
  };
  expect("distinct parameters cannot be interchanged", mutate("second", f => {
    exprOf(stmt(nth(f.body, 0), "return").e, "id").name = "x";
  }), false, "cannot establish T ≤ U");
  expect("a missing dependent bound cannot justify the const", mutate("upper", f => {
    must(f.typeParams[1], "a type parameter").bound = null;
  }), false, "generic binding annotation at");
  expect("dependent inclusion cannot be reversed", mutate("upper", f => {
    must(f.params[0], "a parameter").type = t;
    sole(stmt(nth(f.body, 0), "const")).annot = { top: false, atoms: [{ a: "param", name: "U" }] };
  }), false, "cannot establish T ≤ U");
  expect("a widened const cannot recover the narrower parameter", mutate("upper", f => {
    f.retType = { top: false, atoms: [{ a: "param", name: "U" }] };
  }), false, "cannot establish");
  expect("a broken transitive bound chain cannot reach boolean", mutate("boundChain", f => {
    must(f.typeParams[1], "a type parameter").bound = null;
  }), false, "cannot establish");
  expect("forward and cyclic bounds are refused", mutate("boundChain", f => {
    must(f.typeParams[0], "a type parameter").bound = { top: false, atoms: [{ a: "param", name: "V" }] };
  }), false, "bound must name an earlier parameter");
  expect("duplicate type parameters are refused", mutate("second", f => {
    must(f.typeParams[1], "a type parameter").name = "T";
  }), false, "duplicate type parameter");
  const merged = clone(claims);
  must(functionOf(merged, fileKey, "second").params[1], "a parameter").type = t;
  expect("producer cannot collapse U to T", run(ast, merged), false, "differ from the source annotation");
  const boolean: ClaimType = { top: false, atoms: [{ a: "boolean" }] };
  const editedClaims = (name: string, edit: (f: SkjsFunction) => void) => {
    const changed = clone(rawClaims);
    edit(functionOf(changed, fileKey, name));
    return changed;
  };
  /** One binding of a function's i-th entry, by name. */
  const varOf = (f: SkjsFunction, i: number, name: string) =>
    must(must(f.envs[i], `entry ${i}`).vars.find((v) => v.name === name), `a claim for ${name}`);
  const badEntry = editedClaims("bind", f => {
    varOf(f, 0, "x").type = boolean;
  });
  const badExpression = editedClaims("bind", f => { must(f.exprs[0], "a claim").type = boolean; });
  expect("unjustified entry edit is rejected", run(ast, badEntry), false, "generic entry claim at");
  expect("unjustified expression edit is rejected", run(ast, badExpression), false, "generic expression claim at");
  expect("a const entry cannot regain a narrower dependent type", run(ast, editedClaims("upper", f => {
    varOf(f, 1, "y").type = { top: false, atoms: [{ a: "param", name: "U" }] };
  })), false, "generic entry claim at");
  expect("missing expression claims reject", run(ast, editedClaims("bind", f => { f.exprs.pop(); })), false, "missing, duplicate or unmatched");
  expect("duplicate entry claims reject", run(ast, editedClaims("bind", f => { f.envs.push(clone(must(f.envs[0], "an entry"))); })), false, "duplicate source claim sites or bindings");
  expect("unmatched expression claims reject", run(ast, editedClaims("bind", f => {
    f.exprs.push({ pos: [0, 1], type: t });
  })), false, "claim site is not");
  expect("extra entry bindings reject", run(ast, editedClaims("bind", f => {
    must(f.envs[0], "an entry").vars.push({ name: "invented", type: t });
  })), false, "bindings differ");
  expect("justified weakening along the bound chain verifies", run(ast, editedClaims("boundChain", f => {
    varOf(f, 0, "x").type = boolean;
    must(f.exprs[0], "a claim").type = boolean;
  })), true);
  // Reuse a valid certificate and change only the claims before consumption.
  // This catches a fix confined to production or the viewer.
  for (const [name, changed] of [["entry", badEntry], ["expression", badExpression]] as const) {
    expect("original claims produce evidence", run(ast, rawClaims), true);
    const cp = path.join(tmp, "claims.json");
    fs.writeFileSync(cp, JSON.stringify(changed));
    const r = spawnSync(verifier, ["--check-stateful-source", path.join(tmp, "ast.json"), cp,
      fileKey, path.join(tmp, "evidence.json")], { encoding: "utf8" });
    expect(`consumer rejects edited ${name} claim`, r, false, `generic ${name} claim at`);
  }
  const source = fs.readFileSync(fileKey, "utf8");
  for (const [changed, kind] of [[badEntry, "environment-obligation"], [badExpression, "expression-obligation"]] as const) {
    const report = fromSkjs(source, fileKey, changed, "skjs");
    const { results } = verifySkjs(fileKey, source, changed, fileKey, report, verifier, 8);
    const index = report.functions.findIndex(f => f.name === "bind");
    const result = results[index];
    if (result?.status !== "not-established" || result?.location?.kind !== kind)
      throw Error(`generic claim rejection has no viewer location: ${JSON.stringify(result)}`);
    passed++;
  }
  // Both native producers converge before verification or display.
  const imported=spawnSync(verifier,["--export-source-claims",astPath,claimsPath,fileKey],{encoding:"utf8"});
  assert.equal(imported.status,0,imported.stderr);
  const neutral=JSON.parse(imported.stdout).claims;
  const tsClaims=tscProduce(fileKey).doc;
  closeTsc();
  assert.deepEqual(neutral.functions.slice(0,4),tsClaims.functions.slice(0,4),"both producers use identical rigid-parameter encoding");
  // The Boolean result permits a producer to state a weaker expression claim.
  assert.deepEqual(neutral.types,tsClaims.types);
  const np=path.join(tmp,"neutral.json");
  fs.writeFileSync(np,JSON.stringify(neutral));
  expect("native claims produce common evidence",run(ast,rawClaims),true);
  const consumed=spawnSync(verifier,["--check-source-claims",astPath,np,fileKey,path.join(tmp,"evidence.json")],{encoding:"utf8"});
  expect("neutral claims receive semantic certification",consumed,true);
  neutral.functions[0].expressions[0].type=[1,2];
  fs.writeFileSync(np,JSON.stringify(neutral));
  expect("neutral edit rejects with native-import evidence",spawnSync(verifier,["--check-source-claims",astPath,np,fileKey,path.join(tmp,"evidence.json")],{encoding:"utf8"}),false,"generic expression claim");
  console.log(`Generic bodies: ${passed} passed`);
} catch (e) {
  console.error(e);
  process.exit(1);
}
