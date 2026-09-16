#!/usr/bin/env node
import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { spawnSync } from "node:child_process";
import surface from "../tools/claim-text.mts";
import vm from "node:vm";
import { stripTypes } from "../tools/strip-types.mts";
import type { Ast, Expr, FunctionAst, Stmt } from "../tools/fragment.mts";
import type { Atom, ClaimType, FunctionAtom } from "../tools/claim.mts";
import type { Span } from "../tools/span.mts";
import type { Manifest } from "../report-viewer/types.ts";
import {
  functionOf,
  type SkjsClaims,
  type SkjsExpression,
  type SkjsFunction,
} from "../tools/skjs-claims.mts";
import { at as nth, atom, binding, claimAt, claimType, expr, field, fn, list, must, record, rows, stmt } from "./edits.mts";

const [astPath, claimsPath, fileKey, verifier] = process.argv.slice(2);
const ast: Ast = JSON.parse(fs.readFileSync(astPath, "utf8"));
const claims: SkjsClaims = JSON.parse(fs.readFileSync(claimsPath, "utf8"));
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "callables-"));
const clone = <T,>(x: T): T => structuredClone(x);
const lit = (v: string): ClaimType => ({top: false, atoms: [{a: "booleanlit", v}]});
let passed = 0;

/** A claim addressed by the expression it is about, which is how every
 * alteration below reaches one. */
type At = (e: { pos: Span }) => SkjsExpression;
/** A fresh copy of the pair, and the one function each check is about. */
const about = (name: string) => {
  const a = clone(ast), c = clone(claims);
  const f = fn(a, name), fc = functionOf(c, fileKey, name);
  const at: At = (e) => claimAt(fc, e.pos);
  return { a, c, f, fc, at };
};
type Apply = Extract<Expr, { k: "apply" }>;
type Bin = Extract<Expr, { k: "bin" }>;
type Conditional = Extract<Expr, { k: "conditional" }>;
type LetBody = Extract<Expr, { k: "letBody" }>;
type IfBody = Extract<Expr, { k: "ifBody" }>;
type Write = Extract<Expr, { k: "write" }>;
/** One actual of a call, which several alterations replace or re-claim. */
const nthArg = (call: Apply, i: number): Expr =>
  must(call.args[i], `argument ${i}`);
/** The body of a closure bound by the i-th statement, which is where these
 * fixtures put the construct under test. */
const closure = (f: FunctionAst, i: number) =>
  expr(stmt(nth(f.body, i), "const").init, "lambda").body;
/** The `if` a fixture guards with, and the closure its else arm returns. */
type Branch = Extract<Stmt, { k: "if" }>;
const escaping = (branch: Branch) =>
  expr(stmt(nth(must(branch.else_, "an else arm"), 0), "return").e, "lambda");
/** The binding a lowered `let` body introduces inside another. */
const inner = (b: LetBody) => expr(b.body, "letBody");
/** The arrows a claim states, where a fixture exports one alternative each. */
const callableAlternatives = (claim: SkjsExpression): FunctionAtom[] => {
  const atoms = claimType(claim).atoms;
  assertCallableAlternatives(atoms);
  return atoms.map((a) => atom(a, "function"));
};
/** The call whose argument is itself an assignment. */
const writingCall = (body: Stmt[]) =>
  expr(stmt(nth(body, 2), "const").init, "apply");
/** The assignment a nested call passes as its argument. */
const nestedWrite = (call: Apply): Write => expr(nthArg(call, 0), "write");
/** Pass `false` where the fixture passes `true`, claim included. */
const falseArgument = (call: Apply, at: At) => {
  const arg = nthArg(call, 0);
  expr(arg, "lit").lit = {a: "booleanlit", v: "false"};
  at(arg).type = lit("false");
};

function run(mode: string, a: Ast, c: SkjsClaims, evidence?: unknown) {
  fs.writeFileSync(path.join(tmp, "ast"), JSON.stringify(a));
  fs.writeFileSync(path.join(tmp, "claims"), JSON.stringify(c));
  if (evidence) fs.writeFileSync(path.join(tmp, "evidence"), JSON.stringify(evidence));
  const args = [mode, path.join(tmp, "ast"), path.join(tmp, "claims"), fileKey, path.join(tmp, "evidence")];
  if (mode === "--produce-stateful-source") args.push("10");
  const result = spawnSync(verifier, args, {encoding: "utf8"});
  if (result.error || result.signal) throw result.error || Error(String(result.signal));
  return result;
}

function expect(name: string, result: {status: number | null; stdout: string; stderr: string}, accept: boolean) {
  assert.equal(result.status === 0, accept, `${name}: ${result.stdout}${result.stderr}`);
  passed++;
  console.log(`  ${name}: OK`);
}

try {
  expect("produce callable certificates", run("--produce-stateful-source", ast, claims), true);
  const evidence = JSON.parse(fs.readFileSync(path.join(tmp, "evidence"), "utf8"));
  expect("independent callable consumer", run("--check-stateful-source", ast, claims, evidence), true);

  for(const [name,edit] of rows<[string, (b: Apply, at: At) => void]>([
    ["coalesced callable cannot discard fallback",(b,at)=>{
      const t=claimType(at(b.callee));
      const arrows=t.atoms.filter((a)=>a.a==="function");
      assertCallableAlternatives(arrows);
      t.atoms=[must(arrows.find((a)=>a.result.atoms.some((r)=>r.a==="booleanlit"&&r.v==="true")),"a true-result arrow")];
    }],
    ["coalesced call result cannot narrow",(b,at)=>{at(b).type=lit("true");}],
    ["nullish original cannot be its own fallback",b=>{expr(expr(b.callee,"coalesce").right,"id").name="f";}],
    ["null fallback cannot supply a callable",(b,at)=>{
      const coalesce=expr(b.callee,"coalesce"),r=coalesce.right;at(r).type={top:false,atoms:[{a:"null"}]};
      coalesce.right={k:"lit",pos:r.pos,lit:{a:"null"}};
    }],
    ["coalesced callable checks the argument",(b,at)=>{
      const arg=nthArg(b,0);at(arg).type=lit("true");b.args[0]={k:"lit",pos:arg.pos,lit:{a:"booleanlit",v:"true"}};
    }],
  ])) {
    const {a,c,f,at}=about("coalescedCallable");
    edit(expr(closure(f,0),"apply"),at);
    expect(name,run("--produce-stateful-source",a,c),false);
    expect(`${name} (consumer)`,run("--check-stateful-source",a,c,evidence),false);
  }

  for (const functionName of ["andGuardedCallable", "orGuardedCallable"]) {
    for (const [name, edit] of rows<[string, (b: Bin, at: At) => void]>([
      ["reversed guard cannot justify the call", (b, at) => {
        const test = expr(b.l, "bin");
        test.op = test.op === "===" ? "!==" : "===";
      }],
      ["opposite short-circuit operator cannot justify the call", (b, at) => {
        b.op = b.op === "&&" ? "||" : "&&";
      }],
      ["result must include the skipped branch", (b, at) => {
        const called = at(b.r).type;
        assert.deepEqual(called, lit(functionName === "andGuardedCallable" ? "true" : "false"));
        at(b).type = clone(called);
      }],
    ])) {
      const {a, c, f, at} = about(functionName);
      edit(expr(closure(f, 0), "bin"), at);
      expect(`${functionName}: ${name}`, run("--produce-stateful-source", a, c), false);
      expect(`${functionName}: ${name} (consumer)`, run("--check-stateful-source", a, c, evidence), false);
    }
  }

  for (const [name, edit] of rows<[string, (branch: Branch, at: At) => void]>([
    ["reversed guard cannot justify an escaping capture", (branch, at) => {
      expr(branch.cond, "bin").op = "!==";
    }],
    ["escaping capture must retain both alternatives", (branch, at) => {
      const callee = claimType(at(expr(escaping(branch).body, "apply").callee));
      assertCallableAlternatives(callee.atoms);
      callee.atoms = [must(callee.atoms[0], "an alternative")];
    }],
    ["returned closure signature cannot narrow", (branch, at) => {
      atom(claimType(at(escaping(branch))).atoms[0], "function").result = lit("true");
    }],
    ["later invocation result cannot narrow", (branch, at) => {
      at(escaping(branch).body).type = lit("true");
    }],
  ])) {
    const {a, c, f, at} = about("capturedGuardedCallable");
    edit(stmt(nth(f.body, 0), "if"), at);
    expect(name, run("--produce-stateful-source", a, c), false);
    expect(`${name} (consumer)`, run("--check-stateful-source", a, c, evidence), false);
  }

  for (const [name, edit] of rows<[string, (b: LetBody, at: At, fc: SkjsFunction) => void]>([
    ["alias selection must respect the guard", (b, at, fc) => {
      expr(expr(b.init, "conditional").cond, "bin").op = "!==";
    }],
    ["selected alias cannot make the original callable", (b, at, fc) => {
      expr(expr(inner(b).init, "lambda").body, "apply");
      expr(expr(expr(inner(b).init, "lambda").body, "apply").callee, "id").name = "f";
    }],
    ["alias initializer must retain the fallback", (b, at, fc) => {
      const type = claimType(at(b.init));
      assertCallableAlternatives(type.atoms);
      type.atoms = [must(type.atoms[0], "an alternative")];
    }],
    ["joined alias entry cannot discard an alternative", (b, at, fc) => {
      const type = claimType(binding(fc, inner(b).pos[0], "selected"));
      assertCallableAlternatives(type.atoms);
      type.atoms = [must(type.atoms[0], "an alternative")];
    }],
    ["nested alias call result cannot narrow", (b, at, fc) => {
      at(expr(inner(b).init, "lambda").body).type = lit("true");
    }],
  ])) {
    const {a, c, f, fc, at} = about("aliasedCallableSelection");
    edit(expr(closure(f, 0), "letBody"), at, fc);
    expect(name, run("--produce-stateful-source", a, c), false);
    expect(`${name} (consumer)`, run("--check-stateful-source", a, c, evidence), false);
  }

  for (const [name, edit] of rows<[string, (call: Apply, at: At) => void]>([
    ["argument must fit every selected callable", (call, at) => {
      falseArgument(call, at);
    }],
    ["claimed callee cannot widen a narrow domain", (call, at) => {
      const arrows = callableAlternatives(at(call.callee));
      assert(arrows.some((a) => JSON.stringify(a.params[0]) === JSON.stringify(lit("true"))));
      for (const arrow of arrows) arrow.params[0] = {top: false, atoms: [{a: "boolean"}]};
      falseArgument(call, at);
    }],
    ["callee claim cannot discard the restrictive alternative", (call, at) => {
      const type = claimType(at(call.callee));
      assertCallableAlternatives(type.atoms);
      type.atoms = callableAlternatives(at(call.callee)).filter(
        (a) => must(a.params[0], "a domain").atoms.some((p) => p.a === "boolean"),
      );
      assert.equal(type.atoms.length, 1);
      falseArgument(call, at);
    }],
    ["shared-domain result must retain both alternatives", (call, at) => {
      at(call).type = lit("true");
    }],
  ])) {
    const {a, c, f, at} = about("sharedCallableDomain");
    edit(expr(expr(expr(closure(f, 0), "letBody").body, "returnBody").e, "apply"), at);
    expect(name, run("--produce-stateful-source", a, c), false);
    expect(`${name} (consumer)`, run("--check-stateful-source", a, c, evidence), false);
  }

  for (const [name, edit] of rows<[string, (b: Conditional, at: At) => void]>([
    ["false branch cannot borrow the true-only domain", (b, at) => {
      const [then_, else_] = [expr(b.then, "apply"), expr(b.else_, "apply")];
      assert.deepEqual(at(nthArg(then_, 0)).type, lit("true"));
      assert.deepEqual(at(nthArg(else_, 0)).type, lit("false"));
      expr(else_.callee, "id").name = "narrow";
      at(else_.callee).type = clone(at(then_.callee).type);
      at(else_).type = clone(at(then_).type);
    }],
    ["branch argument claim must match the tested value", (b, at) => {
      at(nthArg(expr(b.else_, "apply"), 0)).type = lit("true");
    }],
    ["branch result must match its own callee", (b, at) => {
      assert.deepEqual(at(b.then).type, lit("false"));
      at(b.then).type = lit("true");
    }],
    ["joined call result cannot retain one branch only", (b, at) => {
      at(b).type = lit("true");
    }],
  ])) {
    const {a, c, f, at} = about("branchLocalCallableDomains");
    edit(expr(closure(f, 0), "conditional"), at);
    expect(name, run("--produce-stateful-source", a, c), false);
    expect(`${name} (consumer)`, run("--check-stateful-source", a, c, evidence), false);
  }

  for (const [name, edit] of rows<[string, (body: Stmt[], at: At) => void]>([
    ["argument write must satisfy the callee domain", (body, at) => {
      atom(claimType(at(writingCall(body).callee)).atoms[0], "function").params[0] = lit("true");
    }],
    ["argument write must satisfy the cell invariant", (body, at) => {
      const arg = expr(nthArg(writingCall(body), 0), "write");
      expr(arg.rhs, "lit").lit = {a: "null"};
      at(arg.rhs).type = {top: false, atoms: [{a: "null"}]};
      at(arg).type = clone(at(arg.rhs).type);
    }],
    ["assignment argument must return its RHS", (body, at) => {
      at(nthArg(writingCall(body), 0)).type = {top: false, atoms: [{a: "null"}]};
    }],
    ["captured read cannot invent a singleton", (body, at) => {
      at(expr(stmt(nth(body, 1), "const").init, "lambda").body).type = lit("true");
    }],
  ])) {
    const {a, c, f, at} = about("callableArgumentWrite");
    edit(f.body, at);
    expect(name, run("--produce-stateful-source", a, c), false);
    expect(`${name} (consumer)`, run("--check-stateful-source", a, c, evidence), false);
  }

  // The assignment returns false, although the original exporter claims only
  // Boolean. An explicit refinement supports a false-only view of the callee.
  {
    const c = clone(claims);
    const fc = functionOf(c, fileKey, "callableArgumentWrite");
    const at: At = (e) => claimAt(fc, e.pos);
    const call = writingCall(fn(ast, "callableArgumentWrite").body);
    assert.deepEqual(at(nthArg(call, 0)).type, {top: false, atoms: [{a: "boolean"}]});
    at(nthArg(call, 0)).type = lit("false");
    atom(claimType(at(call.callee)).atoms[0], "function").params[0] = lit("false");
    expect("explicit assignment refinement satisfies false-only view", run("--produce-stateful-source", ast, c), true);
    const refined = JSON.parse(fs.readFileSync(path.join(tmp, "evidence"), "utf8"));
    expect("independent refined assignment consumer", run("--check-stateful-source", ast, c, refined), true);
    expect("original evidence cannot replace refined assignment proof", run("--check-stateful-source", ast, c, evidence), false);
  }

  for (const [name, edit] of rows<[string, (call: Apply, at: At) => void]>([
    ["nested argument receiver must remain the captured cell", (call, at) => {
      expr(nestedWrite(call).receiver, "id").name = "next";
    }],
    ["nested argument RHS must retain its parameter contract", (call, at) => {
      at(nestedWrite(call).rhs).type = lit("false");
    }],
    ["nested assignment must return its saved RHS", (call, at) => {
      at(nthArg(call, 0)).type = {top: false, atoms: [{a: "null"}]};
    }],
  ])) {
    const {a, c, f, at} = about("nestedCallableArgumentWrite");
    edit(expr(closure(f, 2), "apply"), at);
    expect(name, run("--produce-stateful-source", a, c), false);
    expect(`${name} (consumer)`, run("--check-stateful-source", a, c, evidence), false);
  }
  {
    const index = ast.functions.findIndex((f) => f.name === "nestedCallableArgumentWrite");
    const variable = (i: number) => ({var: {i}});
    const letE = (a: unknown, b: unknown) => ({letE: {a, b}});
    // Context: next, read, cell, seed. After saving cell, next moves to slot 1;
    // the write consumes saved operands and the assignment returns saved next.
    const expected = letE(variable(2), letE(variable(1),
      letE({writeAt: {field: "value", a: variable(1), b: variable(0)}}, variable(1))));
    const obligations = list(field(evidence, "obligations", index), "the obligations");
    const proof = obligations.findIndex((e) => {
      try { assert.deepEqual(field(e, "node", "claim", "term"), expected); return true; } catch { return false; }
    });
    assert(proof >= 0, "nested argument must retain receiver and named RHS bindings");
    passed++;
    console.log("  nested argument preserves exact lexical slots: OK");
    const changed = clone(evidence);
    // Seed is also Boolean, but substituting it for next changes the program.
    record(
      field(changed, "obligations", index, proof, "node", "claim", "term", "letE", "b", "letE"),
      "the inner binding",
    ).a = variable(4);
    expect("same-typed capture cannot replace argument parameter", run("--check-stateful-source", ast, claims, changed), false);
  }

  for (const [name, edit] of rows<[string, (body: IfBody) => void]>([
    ["returned capture requires the non-null factory branch", (body) => {
      expr(body.cond, "bin").op = "!==";
    }],
    ["factory argument refinement cannot transfer to the caller capture", (body) => {
      expr(expr(expr(body.else_, "returnBody").e, "lambda").body, "id").name = "seed";
    }],
  ])) {
    const a = clone(ast);
    const body = expr(closure(fn(a, "branchReturnedCapture"), 0), "ifBody");
    assert.equal(expr(expr(expr(body.else_, "returnBody").e, "lambda").body, "id").name, "input");
    edit(body);
    expect(name, run("--produce-stateful-source", a, claims), false);
    expect(`${name} (consumer)`, run("--check-stateful-source", a, claims, evidence), false);
  }

  for (const [name, edit] of rows<[string, (f: FunctionAst, at: At) => void]>([
    ["factory result cannot widen the returned parameter domain", (f, at) => {
      const factory = atom(claimType(at(stmt(nth(f.body, 0), "const").init)).atoms[0], "function");
      const returned = atom(factory.result.atoms[0], "function");
      assert.deepEqual(returned.params[0], lit("true"));
      returned.params[0] = {top: false, atoms: [{a: "boolean"}]};
    }],
    ["returned callable requires the shared true-only domain", (f, at) => {
      const call = expr(stmt(nth(f.body, 2), "return").e, "apply");
      assert.deepEqual(at(nthArg(call, 0)).type, lit("true"));
      falseArgument(call, at);
    }],
  ])) {
    const {a, c, f, at} = about("returnedCallableDomain");
    edit(f, at);
    expect(name, run("--produce-stateful-source", a, c), false);
    expect(`${name} (consumer)`, run("--check-stateful-source", a, c, evidence), false);
  }

  for (const [name, edit] of rows<[string, (f: FunctionAst, at: At) => void]>([
    ["factory result claim must retain the null alternative", (f, at) => {
      const result = atom(claimType(at(stmt(nth(f.body, 0), "const").init)).atoms[0], "function").result;
      assert(result.atoms.some((a) => a.a === "null"));
      result.atoms = result.atoms.filter((a) => a.a !== "null");
    }],
    ["returned nullable callable must be invoked on the non-null branch", (f) => {
      const test = expr(expr(stmt(nth(f.body, 2), "return").e, "conditional").cond, "bin");
      assert.equal(test.op, "===");
      test.op = "!==";
    }],
  ])) {
    const {a, c, f, at} = about("nullableFactoryResult");
    edit(f, at);
    expect(name, run("--produce-stateful-source", a, c), false);
    expect(`${name} (consumer)`, run("--check-stateful-source", a, c, evidence), false);
  }

  {
    const a = clone(ast);
    const body = expr(closure(fn(a, "laterGuardedCallback"), 1), "conditional");
    const test = expr(body.cond, "bin");
    assert.equal(expr(test.l, "id").name, "callback");
    // With the inner guard reversed, the call occurs on its null edge. The
    // later outer guard cannot rescue the already-created closure's body.
    test.op = "!==";
    expect("later call-site guard cannot repair the closure's null branch", run("--produce-stateful-source", a, claims), false);
    expect("later call-site guard cannot repair the closure's null branch (consumer)", run("--check-stateful-source", a, claims, evidence), false);
  }

  {
    const a = clone(ast);
    const test = expr(stmt(nth(fn(a, "compoundAbsenceCapture").body, 1), "if").cond, "bin");
    assert.equal(test.op, "||");
    test.op = "&&";
    expect("returning an impossible absence conjunction excludes neither tag", run("--produce-stateful-source", a, claims), false);
    expect("returning an impossible absence conjunction excludes neither tag (consumer)", run("--check-stateful-source", a, claims, evidence), false);
  }

  {
    const a = clone(ast);
    const guarded = stmt(nth(stmt(nth(fn(a, "callbackProbeDoesNotNarrow").body, 2), "if").then, 0), "return");
    // Keep the real call's source span and claim, but remove the caller's guard.
    // The probing callback's Boolean contract supplies no capture refinement.
    guarded.e = expr(guarded.e, "conditional").else_;
    expect("Boolean probe cannot replace the caller's null guard", run("--produce-stateful-source", a, claims), false);
    expect("Boolean probe cannot replace the caller's null guard (consumer)", run("--check-stateful-source", a, claims, evidence), false);
  }

  {
    const runtime = vm.createContext({});
    vm.runInContext(stripTypes(fs.readFileSync(fileKey, "utf8")), runtime, {timeout: 1000});
    for (const seed of [false, true]) {
      assert.equal(vm.runInContext(`selectedCallableAfterMutation(${seed})(null)`, runtime, {timeout: 1000}), false);
    }
    passed++;
    console.log("  JavaScript selection remains stable while the live capture observes mutation: OK");
    const a = clone(ast);
    const callee = expr(expr(closure(fn(a, "selectedCallableAfterMutation"), 4), "apply").callee, "id");
    assert.equal(callee.name, "selected");
    callee.name = "snapshot";
    // The substitute has the same arrow type, so it is still well typed. Its
    // changed lexical binding nevertheless requires freshly generated evidence.
    expect("same-typed snapshot cannot reuse the selected callable's evidence", run("--check-stateful-source", a, claims, evidence), false);
    expect("same-typed snapshot produces its own evidence", run("--produce-stateful-source", a, claims), true);
  }

  const types: unknown[] = [];
  for (const file of claims) for (const f of file.functions) {
    types.push(f.retType, ...f.params.map((p) => p.type), ...f.exprs.map((e) => e.type));
    for (const env of f.envs) types.push(...env.vars.map((v) => v.type));
  }
  assert(types.length > 0);
  for (const type of types) {
    // A type the producer could not decode says so, and is not a claim to
    // print: everything else must survive being printed and read back.
    const unsupported = !!type && typeof type === "object" &&
      "unsupported" in type && type.unsupported;
    if (type && !unsupported && surface.printType(type).printable)
      assert.deepEqual(surface.parseType(surface.printType(type).text), type);
  }
  passed++;
  console.log("  callable claim types survive report round trips: OK");

  const report = path.join(tmp, "callables.annotated.ts");
  const annotated = spawnSync(process.execPath, [
    path.resolve(import.meta.dirname, "../tools/annotate-source.mts"), fileKey,
    "--claims", claimsPath, "--verify", verifier, "--out", report,
  ], {encoding: "utf8"});
  if (annotated.error || annotated.signal) throw annotated.error || Error(String(annotated.signal));
  expect("independently verified callable report", annotated, true);
  const manifest: Manifest = JSON.parse(fs.readFileSync(report + ".json", "utf8"));
  const results = must(manifest.results, "results");
  assert.equal(results.length, ast.functions.length);
  assert(results.every((r) => r.status === "verified" && r.certificateSha256));
  console.log(`Callables: ${passed} passed, 0 failed`);
} finally {
  fs.rmSync(tmp, {recursive: true, force: true});
}

function assertCallableAlternatives(arrows: Atom[]) {
  const results = arrows.map((a) => atom(a, "function").result.atoms);
  if(arrows.length!==2 || !["true","false"].every(v=>results.some(atoms=>
    atoms.length===1 && atoms[0]?.a==="booleanlit" && atoms[0].v===v)))
    throw Error("coalesced fixture must export both distinct callable results");
}
