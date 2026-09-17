import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import vm from "node:vm";
import { spawnSync } from "node:child_process";
import type { SourceClaims } from "../tools/source-claims.mts";
import { stripTypes } from "../tools/strip-types.mts";
import { must } from "./edits.mts";

const [ast, raw, tsc, file, verifier] = process.argv.slice(2);
const work = fs.mkdtempSync(os.tmpdir() + "/named-units-");
const proof = work + "/proof";
const source = fs.readFileSync(file, "utf8");
function run(mode: string, claims: string) {
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
      const r = run(`--${action}-${kind}`, claims);
      assert.equal(r.status, 0, r.stdout + r.stderr);
    }
  }
  const original = fs.readFileSync(proof);
  const claims: SourceClaims = JSON.parse(fs.readFileSync(tsc, "utf8"));
  for (const [name, spelling] of [
    ["namedNull", "absent"],
    ["comparisonOrder", "clear()"],
  ]) {
    for (const wrongType of [[3], [0, 3]]) {
      const changed = structuredClone(claims);
      const fn = must(
        changed.functions.find((f) => f.name === name),
        name,
      );
      const operand = must(
        fn.expressions.find((e) => source.slice(...e.pos) === spelling),
        spelling,
      );
      operand.type = wrongType;
      const input = work + "/changed";
      fs.writeFileSync(input, JSON.stringify(changed));
      for (const action of ["produce", "check"]) {
        fs.writeFileSync(proof, original);
        const r = run(`--${action}-source-claims`, input);
        assert.notEqual(r.status, 0, `${name}: forged singleton accepted`);
        if (wrongType.length === 2)
          assert.match(
            r.stderr + r.stdout,
            /equality requires a null or undefined singleton operand/,
          );
      }
    }
  }
  const context = vm.createContext({});
  vm.runInContext(stripTypes(source), context);
  assert.equal(vm.runInContext("namedNull(null)", context), 0);
  assert.equal(vm.runInContext("namedNull(7)", context), 7);
  assert.equal(vm.runInContext("leftUndefined(undefined)", context), false);
  assert.equal(vm.runInContext("leftUndefined(true)", context), true);
  for (const seed of [true, false]) {
    assert.equal(vm.runInContext(`comparisonOrder(${seed})`, context), true);
  }
  console.log(
    "Named unit comparisons: both producers, independent consumption, forged operands and source evaluation order passed",
  );
} finally {
  fs.rmSync(work, { recursive: true, force: true });
}
