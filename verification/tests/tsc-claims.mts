import fs from "node:fs";
import assert from "node:assert/strict";
import type { SourceClaims } from "../tools/source-claims.mts";
import type { Ast } from "../tools/fragment.mts";
import { at as nth, expr, fn as functionIn, must, stmt } from "./edits.mts";

/** One function's claims in a normalized document, by name. */
const claimsFor = (d: SourceClaims, name: string) =>
  must(d.functions.find((f) => f.name === name), `claims for ${name}`);
import type { Span } from "../tools/span.mts";
import os from "node:os";
import path from "node:path";
import { spawnSync } from "node:child_process";
const __dirname = path.dirname(import.meta.filename);
// What TypeScript's own checker believes, put through the verifier.
//
// `tools/tsc-claims.mts` states tsc's types at every site of a corpus file as a
// producer-neutral claims document; this runs that over the corpus and records
// the verdict per file. The expected verdicts below are policy, the same shape
// as `expectedVerified` in examples.mts: a change here is a change in what one
// checker's claims can be derived from, to be read rather than regenerated.




const verifier = process.argv[2];
if (!verifier) throw Error("usage: tsc-claims.mts <verifier>");
const root = path.resolve(__dirname, "../..");
process.chdir(root);
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "tsc-claims-"));

// Why each file lands where it does. A verified file says tsc's claims are
// derivable in the calculus; a failing one names what stops them.
const expected = {
  "stateful-source/generic-identity": "verified",
  "stateful-source/generic-extends": "verified",
  "stateful-source/generic-aliases": "verified",
  "stateful-source/generic-bodies": "verified",
  // A stateful callback crosses a higher-order parameter boundary.
  "callables/arguments": "verified",
  "callables/cells": "verified",
  "callables/thunks": "verified",
  "callables/arity": "verified",
  "callables/guards": "verified",
  "callables/function-field": "verified",
  "callables/receiver-call": "verified",
  "skjs-incomplete/bound-arguments": "verified",
  "callables/call-objects": "out-of-fragment",
  // Factories return closures that capture either private or shared cells.
  "callables/factories": "verified",
  // Compound absence guards preserve all facts established by their outcome.
  "callables/unions": "verified",
  // tsc's flow narrowing carries these, where SKJS's own claims needed a
  // hand repair at the loop exit or the negation.
  "stateful-source/basic": "verified",
  "stateful-source/cells": "verified",
  "stateful-source/records": "verified",
  "stateful-source/captured-local-guards": "verified",
  "stateful-source/cell-conjunction": "verified",
  "stateful-source/closures": "verified",
  "stateful-source/loops": "verified",
  "stateful-source/loop-transfers": "verified",
  "stateful-source/negation": "verified",
  "stateful-source/null-tests": "verified",
  "stateful-source/undefined": "verified",
  "skjs-incomplete/negated-loop-exit": "verified",
  "skjs-incomplete/null-loop-exit": "verified",
  "skjs-incomplete/singleton-negation": "verified",
  "skjs-incomplete/undefined-completes": "verified",
  "skjs-incomplete/arrow-intersection": "verified",
  // A cell read after a write is true at runtime and tsc types it so; the
  // calculus reads a cell at its invariant unless the point carries a
  // current-content assertion, which this producer does not write.
  "skjs-incomplete/write-refined-read": "failed",
  "stateful-source/primitive-callbacks": "failed",
  // Explicit null guards refine the declared nullable cell and callable contracts.
  "stateful-source/null-guards": "verified",
  // tsc rejects these outright, so its claims describe a program it does not
  // accept; the verifier refusing them says nothing about either checker.
  "skjs-incomplete/empty-domain-escape": "failed",
  "skjs-unsound/never-completes": "failed",
  "skjs-unsound/compound-write-refinement": "failed",
  "skjs-unsound/arrow-intersection": "failed",
  // The finding: tsc accepts this with no diagnostic, and the verifier cannot
  // derive its claim for the read after the callback wrote the cell. The
  // function returns false where it declares true.
  "skjs-unsound/captured-refinement": "failed",
  // A cell parameter with a non-mutable field: outside the source fragment.
  "stateful-source/cell-contracts": "out-of-fragment",
};

const run = (cmd: string, args: string[]) =>
  spawnSync(cmd, args, { encoding: "utf8", timeout: 120000 });
let failures = 0;
for (const [name, want] of Object.entries(expected)) {
  const file = `verification/tests/${name}.ts`;
  const ast = path.join(tmp, "ast.json"),
    claims = path.join(tmp, "claims.json"),
    evidence = path.join(tmp, "evidence.json");
  let got, detail = "";
  const parsed = run(process.execPath, [
    "verification/tools/fragment-parse.mts",
    file,
  ]);
  if (parsed.status !== 0) {
    got = "out-of-fragment";
    detail = (parsed.stderr || "").split("\n")[0];
  } else {
    fs.writeFileSync(ast, parsed.stdout);
    const produced = run(process.execPath, [
      "verification/tools/tsc-claims.mts",
      file,
      "--out",
      claims,
    ]);
    if (produced.status !== 0) {
      got = "producer-error";
      detail = (produced.stderr || "").split("\n")[0];
    } else {
      if (name === "callables/unions") {
        const parsed: Ast = JSON.parse(fs.readFileSync(ast, "utf8"));
        const normalized: SourceClaims = JSON.parse(fs.readFileSync(claims, "utf8"));
        const escaped = functionIn(parsed, "escapedLocalCallback");
        const escapedClaims = claimsFor(normalized, escaped.name);
        const callee = expr(expr(stmt(nth(escaped.body, 2), "return").e, "lambda").body, "apply").callee;
        const calleeClaim = escapedClaims.expressions.find((p) => p.pos[0] === callee.pos[0] && p.pos[1] === callee.pos[1]);
        assert.ok(calleeClaim);
        assert.ok(Array.isArray(calleeClaim.type));
        assert.equal(calleeClaim.type.length, 1);
        assert(!calleeClaim.type.includes(0), "returned closure retains its immutable capture refinement");
        const later = functionIn(parsed, "laterGuardedCallback");
        const laterClaims = claimsFor(normalized, later.name);
        const test = expr(expr(expr(stmt(nth(later.body, 1), "const").init, "lambda").body, "conditional").cond, "bin").l;
        const testClaim = laterClaims.expressions.find((p) => p.pos[0] === test.pos[0] && p.pos[1] === test.pos[1]);
        assert.ok(testClaim);
        assert.ok(Array.isArray(testClaim.type));
        assert(testClaim.type.includes(0), "a later outer guard cannot refine an earlier closure capture");
        const absent = functionIn(parsed, "twoAbsenceCapture");
        const absentClaims = claimsFor(normalized, absent.name);
        const absentRef = expr(expr(expr(stmt(nth(absent.body, 2), "return").e, "lambda").body, "conditional").cond, "bin").l;
        const absentClaim = absentClaims.expressions.find((p) => p.pos[0] === absentRef.pos[0] && p.pos[1] === absentRef.pos[1]);
        assert.ok(absentClaim);
        assert.ok(Array.isArray(absentClaim.type));
        assert(absentClaim.type.includes(0), "eliminating undefined must retain null");
        assert(!absentClaim.type.includes(3), "returned capture retains the outer undefined exclusion");
        const compound = functionIn(parsed, "compoundAbsenceCapture");
        const compoundClaims = claimsFor(normalized, compound.name);
        const compoundCallee = expr(expr(stmt(nth(compound.body, 2), "return").e, "lambda").body, "apply").callee;
        const compoundClaim = compoundClaims.expressions.find((p) => p.pos[0] === compoundCallee.pos[0] && p.pos[1] === compoundCallee.pos[1]);
        assert.ok(compoundClaim);
        assert.ok(Array.isArray(compoundClaim.type));
        assert.equal(compoundClaim.type.length, 1);
        assert(!compoundClaim.type.includes(0) && !compoundClaim.type.includes(3),
          "the compound guard excludes both absence tags before capture");
        const ambiguous = functionIn(parsed, "ambiguousCaptureGuard");
        const ambiguousClaims = claimsFor(normalized, ambiguous.name);
        const ambiguousRef = expr(expr(expr(stmt(nth(stmt(nth(ambiguous.body, 1), "if").then, 0), "return").e, "lambda").body, "conditional").cond, "bin").l;
        const ambiguousClaim = ambiguousClaims.expressions.find((p) => p.pos[0] === ambiguousRef.pos[0] && p.pos[1] === ambiguousRef.pos[1]);
        assert.ok(ambiguousClaim);
        assert.ok(Array.isArray(ambiguousClaim.type));
        assert(ambiguousClaim.type.includes(0), "a successful disjunction must retain the path admitted by flag");
        assert.equal(ambiguousClaim.type.length, 2, "capture retains both null and the callable");
        const probe = functionIn(parsed, "callbackProbeDoesNotNarrow");
        const probeClaims = claimsFor(normalized, probe.name);
        const probedRef = expr(expr(stmt(nth(stmt(nth(probe.body, 2), "if").then, 0), "return").e, "conditional").cond, "bin").l;
        const probedClaim = probeClaims.expressions.find((p) => p.pos[0] === probedRef.pos[0] && p.pos[1] === probedRef.pos[1]);
        assert.ok(probedClaim);
        assert.ok(Array.isArray(probedClaim.type));
        assert(probedClaim.type.includes(0), "a Boolean probe result does not refine the captured callback");
        const fn = functionIn(parsed, "distinctNullableCallbacks");
        const fc = claimsFor(normalized, fn.name);
        assert.ok(fc);
        const at = (e: { pos: Span }) => {
          const site = fc.expressions.find((p) => p.pos[0] === e.pos[0] && p.pos[1] === e.pos[1]);
          assert.ok(site);
        assert.ok(Array.isArray(site.type));
          return site.type;
        };
        const guard = stmt(nth(fn.body, 3), "if");
        const tested = expr(expr(guard.cond, "bin").l, "id");
        assert.equal(tested.name, "second");
        assert(at(tested).includes(0), "guarding first must leave second nullable");
        const firstCall = expr(stmt(nth(guard.then, 0), "return").e, "apply");
        const secondCall = expr(stmt(nth(fn.body, 4), "return").e, "apply");
        assert.equal(expr(firstCall.callee, "id").name, "first");
        assert.equal(expr(secondCall.callee, "id").name, "second");
        const branchEntry = fc.entries.find((entry) => entry.start === nth(guard.then, 0).pos[0]);
        assert.ok(branchEntry);
        assert.deepEqual(branchEntry.bindings.find((binding) => binding.name === "second")?.type, [0],
          "an unmentioned callback retains its own null branch at statement entry");
        for (const call of [firstCall, secondCall]) {
          const labels = at(call.callee);
          assert.equal(labels.length, 1);
          assert(!labels.includes(0), "each callback's own guard removes null");
        }
      }
      const checked = run(verifier, [
        "--produce-source-claims",
        ast,
        claims,
        file,
        evidence,
        "10",
      ]);
      got = checked.status === 0 ? "verified" : "failed";
      if (got === "verified" && ["callables/thunks", "callables/cells", "callables/arguments", "callables/factories", "callables/unions", "stateful-source/null-guards"].includes(name)) {
        const consumed = run(verifier, ["--check-source-claims", ast, claims, file, evidence]);
        if (consumed.status !== 0) {
          got = "consumer-failed";
          detail = consumed.stderr;
        }
      }
      if (got === "verified" && ["stateful-source/generic-identity","stateful-source/generic-bodies"].includes(name)) {
        const original: SourceClaims = JSON.parse(fs.readFileSync(claims,"utf8"));
        const consume = (doc: SourceClaims) => {
          fs.writeFileSync(claims,JSON.stringify(doc));
          return run(verifier,["--check-source-claims",ast,claims,file,evidence]);
        };
        assert.equal(consume(original).status,0,"independent generic consumer");
        const mutate = (change: (doc: SourceClaims)=>void) => {
          const doc=structuredClone(original); change(doc);
          assert.notEqual(consume(doc).status,0,"saved evidence must reject changed generic claims");
        };
        mutate(d=>{d.functions[0].expressions[0].type=[1,2];});
        mutate(d=>{d.functions[0].entries[0].bindings[0].type={param:"NotInScope"};});
        mutate(d=>{d.functions[0].expressions.pop();});
        mutate(d=>{d.functions[0].expressions[0].current=[["value",[1]]];});
        if(name.endsWith("generic-bodies")) {
          mutate(d=>{claimsFor(d,"second").result={param:"T"};});
          const weak=structuredClone(original);
          const chain=claimsFor(weak,"boundChain");
          chain.entries[0].bindings[0].type=[1,2];
          chain.expressions[0].type=[1,2];
          assert.equal(consume(weak).status,0,"declared bound chain permits Boolean weakening");
        }
        fs.writeFileSync(claims,JSON.stringify(original));
      }
      if (got === "failed")
        detail = (checked.stderr || "").split("\n")[0].replace(/^reject: /, "");
    }
  }
  if (got === want) {
    console.log(`  ${name}: ${got}${detail ? ` — ${detail.slice(0, 60)}` : ""}`);
  } else {
    failures++;
    console.log(`  ${name}: expected ${want}, got ${got} — ${detail}`);
  }
}
fs.rmSync(tmp, { recursive: true, force: true });
const total = Object.keys(expected).length;
console.log(
  `TypeScript claims: ${total - failures} as expected, ${failures} changed`,
);
process.exit(failures ? 1 : 0);
