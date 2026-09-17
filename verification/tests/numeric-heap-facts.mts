import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import vm from "node:vm";
import { spawnSync } from "node:child_process";
import { stripTypes } from "../tools/strip-types.mts";
import { fileOf, type SkjsClaims } from "../tools/skjs-claims.mts";
import type { Ast } from "../tools/fragment.mts";
import type { SourceClaims } from "../tools/source-claims.mts";
import { must } from "./edits.mts";

const [ast, raw, tsc, file, verifier] = process.argv.slice(2);
const work = fs.mkdtempSync(os.tmpdir() + "/numeric-heap-");
const proof = work + "/proof";
const source = fs.readFileSync(file, "utf8");
function run(mode: string, claims: string, astPath = ast) {
  const args = [mode, astPath, claims, file, proof];
  if (mode.startsWith("--produce")) args.push("10");
  const r = spawnSync(verifier, args, { encoding: "utf8", timeout: 30000 });
  assert(!r.error && !r.signal, String(r.error || r.signal));
  return r;
}
try {
  for (const [kind, path] of [
    ["stateful-source", raw],
    ["source-claims", tsc],
  ]) {
    let astPath = ast,
      input = path;
    if (kind === "source-claims") {
      // TS does not export field-current assertions. Its broadened field read
      // cannot establish this snapshot; keep that separate producer boundary.
      const boundary = run("--produce-source-claims", path);
      assert.notEqual(boundary.status, 0);
      assert.match(boundary.stderr, /binding-annotation/);
      const selectedAst: Ast = JSON.parse(fs.readFileSync(ast, "utf8"));
      selectedAst.functions = selectedAst.functions.filter(
        (f) => f.name !== "numericAliasSnapshot",
      );
      const selected: SourceClaims = JSON.parse(fs.readFileSync(input, "utf8"));
      selected.functions = selected.functions.filter(
        (f) => f.name !== "numericAliasSnapshot",
      );
      astPath = work + "/ts.ast";
      input = work + "/ts.claims";
      fs.writeFileSync(astPath, JSON.stringify(selectedAst));
      fs.writeFileSync(input, JSON.stringify(selected));
    }
    for (const action of ["produce", "check"]) {
      const r = run(`--${action}-${kind}`, input, astPath);
      assert.equal(r.status, 0, r.stdout + r.stderr);
    }
    const valid = fs.readFileSync(proof);
    const entry = source.indexOf(
      "return read();",
      source.indexOf("function numericGuardedCapture"),
    );
    const changedPath = work + "/changed";
    // After the reset, even an unused binding's entry claim must not retain
    // the previous numeric contents. Neither producer can authorize that claim.
    if (kind === "stateful-source") {
      const changed: SkjsClaims = JSON.parse(fs.readFileSync(input, "utf8"));
      const f = must(
        fileOf(changed, file).functions.find(
          (f) => f.name === "numericGuardedCapture",
        ),
        "function",
      );
      const env = must(
        f.envs.find((e) => e.pos[0] === entry),
        "return environment",
      );
      must(
        env.vars.find((v) => v.name === "value"),
        "value",
      ).type = { top: false, atoms: [{ a: "number" }] };
      fs.writeFileSync(changedPath, JSON.stringify(changed));
    } else {
      const changed: SourceClaims = JSON.parse(fs.readFileSync(input, "utf8"));
      const f = must(
        changed.functions.find((f) => f.name === "numericGuardedCapture"),
        "function",
      );
      const env = must(
        f.entries.find((e) => e.start === entry),
        "return environment",
      );
      const number = changed.types.findIndex(
        (row) => row.length === 1 && row[0] === "num",
      );
      assert(number >= 0);
      must(
        env.bindings.find((v) => v.name === "value"),
        "value",
      ).type = [number];
      fs.writeFileSync(changedPath, JSON.stringify(changed));
    }
    for (const action of ["produce", "check"]) {
      fs.writeFileSync(proof, valid);
      const r = run(`--${action}-${kind}`, changedPath, astPath);
      assert.notEqual(r.status, 0, "stale numeric entry accepted");
    }
  }
  const context = vm.createContext({});
  vm.runInContext(stripTypes(source), context);
  const evaluate = (expression: string) => vm.runInContext(expression, context);
  assert.equal(evaluate("numericGuardedCapture()"), 0);
  for (const seed of ["17", "-0", "NaN", "Infinity"]) {
    assert(
      Object.is(evaluate(`numericAssignmentSnapshot(${seed})`), evaluate(seed)),
    );
    assert(
      Object.is(evaluate(`numericAliasSnapshot(${seed})`), evaluate(seed)),
    );
  }
  assert.equal(evaluate("numericAliasSnapshot(null)"), 0);
  console.log(
    "Numeric heap facts: both producers, stale-entry rejection, numeric snapshots and the TS field-claim boundary passed",
  );
} finally {
  fs.rmSync(work, { recursive: true, force: true });
}
