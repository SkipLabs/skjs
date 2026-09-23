import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import vm from "node:vm";
import { spawnSync } from "node:child_process";
import type { Ast } from "../tools/fragment.mts";
import type { SourceClaims } from "../tools/source-claims.mts";
import { stripTypes } from "../tools/strip-types.mts";
import { must, expr, sourceType, stmt } from "./edits.mts";

const [astPath, raw, tsc, file, verifier] = process.argv.slice(2);
const work = fs.mkdtempSync(os.tmpdir() + "/nullish-assignment-");
const proof = work + "/proof";
function run(action: string, kind: string, ast: string, claims: string) {
  const args = [`--${action}-${kind}`, ast, claims, file, proof];
  if (action === "produce") args.push("10");
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
      const r = run(action, kind, astPath, claims);
      assert.equal(r.status, 0, r.stdout + r.stderr);
    }
  }
  const valid = fs.readFileSync(proof);
  const originalAst: Ast = JSON.parse(fs.readFileSync(astPath, "utf8"));
  const original: SourceClaims = JSON.parse(fs.readFileSync(tsc, "utf8"));
  for (const mutation of ["read", "result", "write"]) {
    const ast = structuredClone(originalAst),
      doc = structuredClone(original);
    const f = must(
      ast.functions.find((f) => f.name === "localFallback"),
      "function",
    );
    const fc = must(
      doc.functions.find((c) => c.name === f.name),
      "claims",
    );
    const assignment = expr(stmt(f.body[0], "effect").e, "nullishAssign");
    const at = (pos: [number, number]) =>
      must(
        fc.expressions.find((e) => e.pos[0] === pos[0] && e.pos[1] === pos[1]),
        "expression",
      );
    if (mutation === "read") {
      // A forged non-nullish read must not make the fallback disappear.
      at(assignment.namePos).type = at(assignment.pos).type;
    } else if (mutation === "result") {
      // The present arm can return any number, not just the fallback singleton.
      at(assignment.pos).type = at(assignment.rhs.pos).type;
    } else {
      // Honest Boolean claims still cannot write Boolean into numeric storage.
      assignment.rhs = {
        k: "lit",
        pos: assignment.rhs.pos,
        lit: { a: "booleanlit", v: "true" },
      };
      at(assignment.rhs.pos).type = [1];
      const number = doc.types.findIndex(
        (row) => row.length === 1 && row[0] === "num",
      );
      assert(number >= 0);
      at(assignment.pos).type = [1, number];
      // Permit either result at every later interface, isolating the storage
      // contract rather than rejecting merely at the function's return type.
      f.retType = sourceType({
        top: false,
        atoms: [{ a: "booleanlit", v: "true" }, { a: "number" }],
      });
      fc.result = [1, number];
      const returned = stmt(f.body[1], "return");
      at(returned.e.pos).type = [1, number];
      const entry = must(
        fc.entries.find((e) => e.start === returned.pos[0]),
        "return entry",
      );
      must(
        entry.bindings.find((b) => b.name === "value"),
        "value",
      ).type = [1, number];
    }
    const ap = work + "/ast",
      cp = work + "/claims";
    fs.writeFileSync(ap, JSON.stringify(ast));
    fs.writeFileSync(cp, JSON.stringify(doc));
    for (const action of ["produce", "check"]) {
      fs.writeFileSync(proof, valid);
      const r = run(action, "source-claims", ap, cp);
      assert.notEqual(r.status, 0, `${mutation}: invalid claim accepted`);
      if (action === "produce" && mutation === "write")
        assert.match(r.stderr, /storage-contract/);
    }
  }
  const context = vm.createContext({});
  vm.runInContext(stripTypes(fs.readFileSync(file, "utf8")), context);
  const evaluate = (source: string) => vm.runInContext(source, context);
  for (const n of ["0", "-0", "17", "NaN", "Infinity"]) {
    assert(Object.is(evaluate(`localFallback(${n})`), evaluate(n)));
    assert(Object.is(evaluate(`nestedFallback(${n}, undefined)`), evaluate(n)));
    assert(Object.is(evaluate(`nestedFallback(null, ${n})`), evaluate(n)));
  }
  assert.equal(evaluate("localFallback(null)"), 1);
  assert.equal(evaluate("nestedFallback(null, undefined)"), 2);
  assert.equal(evaluate("skippedFallback(false)"), false);
  assert.equal(evaluate("skippedFallback(true)"), false);
  assert.equal(evaluate("skippedFallback(undefined)"), true);
  assert.equal(
    evaluate("const fill = capturedFallback(null); fill(); fill()"),
    3,
  );
  assert.equal(evaluate("capturedFallback(0)()"), 0);
  console.log(
    "Nullish assignment: both producers and consumers, checked branch claims, storage contract, skipped RHS, nested and captured locals passed",
  );
} finally {
  fs.rmSync(work, { recursive: true, force: true });
}
