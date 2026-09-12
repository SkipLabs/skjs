import fs from "node:fs";
import assert from "node:assert/strict";
import type { SourceClaims } from "../tools/source-claims.mts";
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
  // Callable-valued arguments still use the primitive-only parameter decoder.
  "callables/arguments": "failed",
  // Factories return closures that capture either private or shared cells.
  "callables/factories": "verified",
  // Compound absence guards preserve all facts established by their outcome.
  "callables/unions": "verified",
  // tsc's flow narrowing carries these, where SKJS's own claims needed a
  // hand repair at the loop exit or the negation.
  "stateful-source/basic": "verified",
  "stateful-source/cells": "verified",
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

const run = (cmd: any, args: string[]) =>
  spawnSync(cmd, args, { encoding: "utf8", timeout: 120000 });
let failures = 0;
for (const [name, want] of Object.entries(expected)) {
  const file = `verification/tests/${name}.ts`;
  const ast = path.join(tmp, "ast.json"),
    claims = path.join(tmp, "claims.json"),
    evidence = path.join(tmp, "evidence.json");
  let got, detail = "";
  const parsed = run(process.execPath, [
    "verification/tools/parse-source.mts",
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
        const parsed = JSON.parse(fs.readFileSync(ast, "utf8"));
        const normalized: SourceClaims = JSON.parse(fs.readFileSync(claims, "utf8"));
        const escaped = parsed.functions.find((f: any) => f.name === "escapedLocalCallback");
        const escapedClaims = normalized.functions.find((f) => f.name === escaped.name)!;
        const callee = escaped.body[2].e.body.callee;
        const calleeClaim = escapedClaims.expressions.find((p) => p.pos[0] === callee.pos[0] && p.pos[1] === callee.pos[1]);
        assert.ok(calleeClaim);
        assert.equal(calleeClaim.type.length, 1);
        assert(!calleeClaim.type.includes(0), "returned closure retains its immutable capture refinement");
        const later = parsed.functions.find((f: any) => f.name === "laterGuardedCallback");
        const laterClaims = normalized.functions.find((f) => f.name === later.name)!;
        const test = later.body[1].init.body.cond.l;
        const testClaim = laterClaims.expressions.find((p) => p.pos[0] === test.pos[0] && p.pos[1] === test.pos[1]);
        assert.ok(testClaim);
        assert(testClaim.type.includes(0), "a later outer guard cannot refine an earlier closure capture");
        const absent = parsed.functions.find((f: any) => f.name === "twoAbsenceCapture");
        const absentClaims = normalized.functions.find((f) => f.name === absent.name)!;
        const absentRef = absent.body[2].e.body.cond.l;
        const absentClaim = absentClaims.expressions.find((p) => p.pos[0] === absentRef.pos[0] && p.pos[1] === absentRef.pos[1]);
        assert.ok(absentClaim);
        assert(absentClaim.type.includes(0), "eliminating undefined must retain null");
        assert(!absentClaim.type.includes(3), "returned capture retains the outer undefined exclusion");
        const compound = parsed.functions.find((f: any) => f.name === "compoundAbsenceCapture");
        const compoundClaims = normalized.functions.find((f) => f.name === compound.name)!;
        const compoundCallee = compound.body[2].e.body.callee;
        const compoundClaim = compoundClaims.expressions.find((p) => p.pos[0] === compoundCallee.pos[0] && p.pos[1] === compoundCallee.pos[1]);
        assert.ok(compoundClaim);
        assert.equal(compoundClaim.type.length, 1);
        assert(!compoundClaim.type.includes(0) && !compoundClaim.type.includes(3),
          "the compound guard excludes both absence tags before capture");
        const ambiguous = parsed.functions.find((f: any) => f.name === "ambiguousCaptureGuard");
        const ambiguousClaims = normalized.functions.find((f) => f.name === ambiguous.name)!;
        const ambiguousRef = ambiguous.body[1].then[0].e.body.cond.l;
        const ambiguousClaim = ambiguousClaims.expressions.find((p) => p.pos[0] === ambiguousRef.pos[0] && p.pos[1] === ambiguousRef.pos[1]);
        assert.ok(ambiguousClaim);
        assert(ambiguousClaim.type.includes(0), "a successful disjunction must retain the path admitted by flag");
        assert.equal(ambiguousClaim.type.length, 2, "capture retains both null and the callable");
        const probe = parsed.functions.find((f: any) => f.name === "callbackProbeDoesNotNarrow");
        const probeClaims = normalized.functions.find((f) => f.name === probe.name)!;
        const probedRef = probe.body[2].then[0].e.cond.l;
        const probedClaim = probeClaims.expressions.find((p) => p.pos[0] === probedRef.pos[0] && p.pos[1] === probedRef.pos[1]);
        assert.ok(probedClaim);
        assert(probedClaim.type.includes(0), "a Boolean probe result does not refine the captured callback");
        const fn = parsed.functions.find((f: any) => f.name === "distinctNullableCallbacks");
        const fc = normalized.functions.find((f) => f.name === fn.name)!;
        assert.ok(fc);
        const at = (e: any) => {
          const site = fc.expressions.find((p) => p.pos[0] === e.pos[0] && p.pos[1] === e.pos[1]);
          assert.ok(site);
          return site.type;
        };
        assert.equal(fn.body[3].cond.l.name, "second");
        assert(at(fn.body[3].cond.l).includes(0), "guarding first must leave second nullable");
        const firstCall = fn.body[3].then[0].e;
        const secondCall = fn.body[4].e;
        assert.equal(firstCall.callee.name, "first");
        assert.equal(secondCall.callee.name, "second");
        const branchEntry = fc.entries.find((entry) => entry.start === fn.body[3].then[0].pos[0]);
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
      if (got === "verified" && ["callables/factories", "callables/unions", "stateful-source/null-guards"].includes(name)) {
        const consumed = run(verifier, ["--check-source-claims", ast, claims, file, evidence]);
        if (consumed.status !== 0) {
          got = "consumer-failed";
          detail = consumed.stderr;
        }
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
