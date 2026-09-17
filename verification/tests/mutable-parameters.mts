import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import vm from "node:vm";
import { spawnSync } from "node:child_process";
import type { Ast } from "../tools/fragment.mts";
import type { SourceClaims } from "../tools/source-claims.mts";
import { stripTypes } from "../tools/strip-types.mts";
import { must, stmt, expr } from "./edits.mts";

const [astPath, raw, tsc, file, verifier] = process.argv.slice(2);
const work = fs.mkdtempSync(os.tmpdir() + "/mutable-parameters-");
const proof = work + "/proof";
function run(mode: string, ast: string, claims: string) {
  const args = [mode, ast, claims, file, proof];
  if (mode.startsWith("--produce")) args.push("10");
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
      const r = run(`--${action}-${kind}`, astPath, claims);
      assert.equal(r.status, 0, r.stdout + r.stderr);
    }
  }
  const original = fs.readFileSync(proof);
  const ast: Ast = JSON.parse(fs.readFileSync(astPath, "utf8"));
  const doc: SourceClaims = JSON.parse(fs.readFileSync(tsc, "utf8"));
  const f = must(
    ast.functions.find((f) => f.name === "independentParameters"),
    "function",
  );
  const fc = must(
    doc.functions.find((f) => f.name === "independentParameters"),
    "claims",
  );
  const assignment = expr(stmt(f.body[0], "effect").e, "assign");
  // The RHS and assignment really are null. The declared Boolean storage
  // contract must reject the write even when the producer reports it honestly.
  const [start, end] = assignment.rhs.pos;
  fc.expressions = fc.expressions.filter(
    (e) =>
      !(
        e.pos[0] >= start &&
        e.pos[1] <= end &&
        (e.pos[0] !== start || e.pos[1] !== end)
      ),
  );
  assignment.rhs = { k: "lit", pos: assignment.rhs.pos, lit: { a: "null" } };
  for (const pos of [assignment.pos, assignment.rhs.pos]) {
    must(
      fc.expressions.find((e) => e.pos[0] === pos[0] && e.pos[1] === pos[1]),
      "expression",
    ).type = [0];
  }
  const changedAst = work + "/ast",
    changedClaims = work + "/claims";
  fs.writeFileSync(changedAst, JSON.stringify(ast));
  fs.writeFileSync(changedClaims, JSON.stringify(doc));
  for (const action of ["produce", "check"]) {
    fs.writeFileSync(proof, original);
    const r = run(`--${action}-source-claims`, changedAst, changedClaims);
    assert.notEqual(r.status, 0, "out-of-contract parameter write accepted");
    if (action === "produce") assert.match(r.stderr, /evidence search failed/);
  }
  const context = vm.createContext({});
  vm.runInContext(stripTypes(fs.readFileSync(file, "utf8")), context);
  assert.equal(vm.runInContext("unrelatedFact(null, 7)", context), 7);
  assert.equal(vm.runInContext("unrelatedFact(7, null)", context), 0);
  for (const left of [true, false]) {
    for (const right of [true, false])
      for (const keep of [true, false])
        assert.equal(
          vm.runInContext(
            `independentParameters(${left}, ${keep}, ${right})`,
            context,
          ),
          keep ? !left : !right,
        );
    assert.equal(vm.runInContext(`capturedParameter(${left})`, context), left);
  }
  console.log(
    "Mutable parameters: both producers, independent consumption, storage contracts and capture behavior passed",
  );
} finally {
  fs.rmSync(work, { recursive: true, force: true });
}
