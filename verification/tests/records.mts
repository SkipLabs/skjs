import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import vm from "node:vm";
import { spawnSync } from "node:child_process";
import type { Ast } from "../tools/fragment.mts";
import type { SourceClaims } from "../tools/source-claims.mts";
import { stripTypes } from "../tools/strip-types.mts";
import { expr, must, sole, stmt } from "./edits.mts";

const [astPath, claimsPath, file, verifier, rawClaimsPath] =
  process.argv.slice(2);
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
  if (rawClaimsPath) {
    for (const mode of [
      "--produce-stateful-source",
      "--check-stateful-source",
    ]) {
      const args = [mode, astPath, rawClaimsPath, file, proof];
      if (mode === "--produce-stateful-source") args.push("10");
      const r = spawnSync(verifier, args, { encoding: "utf8" });
      assert(!r.error && !r.signal, String(r.error || r.signal));
      assert.equal(r.status, 0, r.stdout + r.stderr);
    }
    const converted = run("--check-source-claims", claims);
    assert.equal(converted.status, 0, converted.stdout + converted.stderr);
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
  // Dropping a required field cannot be hidden by keeping the field count.
  {
    const swapped = structuredClone(ast);
    const f = must(
      swapped.functions.find((f) => f.name === "recordAlias"),
      "recordAlias",
    );
    const literal = expr(
      sole(stmt(must(f.body[0], "the allocation"), "const")).init,
      "alloc",
    );
    const [left, right] = literal.fields;
    literal.fields = [
      must(left, "the first field"),
      { ...must(right, "the second field"), name: "missing" },
    ];
    const swappedPath = path.join(work, "swapped.ast");
    fs.writeFileSync(swappedPath, JSON.stringify(swapped));
    fs.writeFileSync(input, JSON.stringify(claims));
    for (const mode of ["--produce-source-claims", "--check-source-claims"]) {
      const args = [mode, swappedPath, input, file, proof];
      if (mode === "--produce-source-claims") args.push("10");
      const r = spawnSync(verifier, args, { encoding: "utf8" });
      assert(!r.error && !r.signal, String(r.error || r.signal));
      assert.notEqual(r.status, 0, "a missing required field must not match the contract");
    }
  }
  // What a record may not be, refused while parsing rather than lowered into
  // something the model would then have to interpret.
  for (const [name, text] of [
    ["a duplicate field in a type", "const x: { a: boolean; a: boolean } = { a: true }; return null;"],
    ["a duplicate field in a literal", "const x: { a: boolean } = { a: true, a: false }; return null;"],
    ["a type with no field", "const x: {} = {}; return null;"],
    ["a literal with no field", "const x: { a: boolean } = {}; return null;"],
  ] satisfies [string, string][]) {
    const probe = path.join(work, "gated.ts");
    fs.writeFileSync(probe, `function gated(): null { ${text} }`);
    const r = spawnSync(
      process.execPath,
      ["verification/tools/fragment-parse.mts", probe],
      { encoding: "utf8" },
    );
    assert(!r.error && !r.signal, String(r.error || r.signal));
    assert.notEqual(r.status, 0, name);
    assert(r.stderr.startsWith("gate:"), name + ": " + r.stderr);
  }
  console.log(
    "  seven multi-field programs verify and independently consume, numeric and single named fields among them; runtime order, aliases, guards and .call agree; three forged observations, one missing field and four malformed records rejected",
  );
} finally {
  fs.rmSync(work, { recursive: true, force: true });
}
