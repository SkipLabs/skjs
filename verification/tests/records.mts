import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import vm from "node:vm";
import { spawnSync } from "node:child_process";
import type { Ast } from "../tools/fragment.mts";
import type { SourceClaims } from "../tools/source-claims.mts";
import { stripTypes } from "../tools/strip-types.mts";
import { must, stmt, expr } from "./edits.mts";

const [astPath, claimsPath, file, verifier] = process.argv.slice(2);
const ast: Ast = JSON.parse(fs.readFileSync(astPath, "utf8"));
const claims: SourceClaims = JSON.parse(fs.readFileSync(claimsPath, "utf8"));
const work = fs.mkdtempSync(path.join(os.tmpdir(), "records-"));
try {
  const input = path.join(work, "claims.json"),
    proof = path.join(work, "proof.json");
  function run(mode: string, doc: SourceClaims) {
    fs.writeFileSync(input, JSON.stringify(doc));
    const args = [mode, astPath, input, file, proof];
    if (mode === "--produce-source-claims") args.push("10");
    const r = spawnSync(verifier, args, { encoding: "utf8" });
    assert(!r.error && !r.signal, String(r.error || r.signal));
    return r;
  }
  for (const mode of ["--produce-source-claims", "--check-source-claims"]) {
    const r = run(mode, claims);
    assert.equal(r.status, 0, r.stdout + r.stderr);
  }
  const original = fs.readFileSync(proof);
  // Check the source-to-calculus boundary as well as the proof: a valid proof
  // of a program with renamed fields would not establish this source program.
  let reorderedAllocations = 0;
  function checkAllocation(value: unknown): void {
    if (!value || typeof value !== "object") return;
    if ("makeAt" in value) {
      const allocation = value.makeAt;
      if (
        allocation &&
        typeof allocation === "object" &&
        "call" in allocation
      ) {
        const code = allocation.call;
        if (code && typeof code === "object" && "closure" in code) {
          const closure = code.closure;
          if (
            closure &&
            typeof closure === "object" &&
            "arity" in closure &&
            closure.arity === 0 &&
            "names" in allocation &&
            Array.isArray(allocation.names) &&
            allocation.names.length === 2 &&
            "inits" in allocation
          ) {
            assert.deepEqual(allocation.names, ["left", "right"]);
            assert.deepEqual(allocation.inits, ["fls", "tru"]);
            reorderedAllocations++;
          }
        }
      }
    }
    Object.values(value).forEach(checkAllocation);
  }
  checkAllocation(JSON.parse(original.toString()));
  assert(
    reorderedAllocations > 0,
    "checked callable allocation must retain field names and source order",
  );
  const context = vm.createContext({});
  vm.runInContext(stripTypes(fs.readFileSync(file, "utf8")), context);
  for (const seed of [false, true]) {
    assert.equal(vm.runInContext(`recordAlias(${seed})`, context), seed);
    assert.equal(vm.runInContext(`recordGuard(${seed})`, context), seed);
    assert.equal(vm.runInContext(`callableRecord(${seed})`, context), seed);
  }
  assert.equal(vm.runInContext("recordGuard(null)", context), false);
  assert.equal(vm.runInContext("recordOrder()", context), false);
  assert.equal(vm.runInContext("reorderedCallable()", context), false);
  for (const [name, field, labels] of [
    ["a write to right cannot narrow left", "left", [1]],
    ["an alias write invalidates right's initial false", "right", [2]],
    ["a missing field cannot carry an observation", "missing", [1, 2]],
  ] satisfies [string, string, number[]][]) {
    const doc = structuredClone(claims);
    const f = must(
      ast.functions.find((f) => f.name === "recordAlias"),
      "recordAlias",
    );
    const ret = stmt(must(f.body.at(-1), "return"), "return");
    const receiver = expr(ret.e, "read").e;
    const fc = must(
      doc.functions.find((f) => f.name === "recordAlias"),
      "claims",
    );
    const point = must(
      fc.expressions.find(
        (e) => e.pos[0] === receiver.pos[0] && e.pos[1] === receiver.pos[1],
      ),
      "receiver claim",
    );
    point.current = [[field, labels]];
    fs.writeFileSync(proof, original);
    assert.notEqual(run("--check-source-claims", doc).status, 0, name);
    assert.notEqual(run("--produce-source-claims", doc).status, 0, name);
  }
  console.log(
    "  five multi-field programs verify and independently consume; runtime order, aliases, guards and .call agree; three forged observations rejected",
  );
} finally {
  fs.rmSync(work, { recursive: true, force: true });
}
