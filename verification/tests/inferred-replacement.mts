import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import vm from "node:vm";
import { spawnSync } from "node:child_process";
import type { SourceClaims } from "../tools/source-claims.mts";
import { stripTypes } from "../tools/strip-types.mts";
import { must } from "./edits.mts";

const [ast, raw, tsc, file, verifier] = process.argv.slice(2);
const work = fs.mkdtempSync(os.tmpdir() + "/inferred-replacement-");
const evidence = work + "/proof";
function run(action: string, kind: string, claims: string) {
  const args = [`--${action}-${kind}`, ast, claims, file, evidence];
  if (action === "produce") args.push("10");
  const result = spawnSync(verifier, args, {
    encoding: "utf8",
    timeout: 30000,
  });
  assert(
    !result.error && !result.signal,
    String(result.error || result.signal),
  );
  return result;
}
try {
  for (const [kind, claims] of [
    ["stateful-source", raw],
    ["source-claims", tsc],
  ]) {
    for (const action of ["produce", "check"]) {
      const r = run(action, kind, claims);
      assert.equal(r.status, 0, r.stdout + r.stderr);
    }
  }
  const original = fs.readFileSync(evidence);
  const doc: SourceClaims = JSON.parse(fs.readFileSync(tsc, "utf8"));
  const source = fs.readFileSync(file, "utf8");
  const f = must(
    doc.functions.find((f) => f.name === "checkedMutableObjectReplacement"),
    "function",
  );
  const returned = source.indexOf("return cell.value");
  const entry = must(
    f.entries.find((e) => e.start === returned),
    "guarded return",
  );
  // The field is Boolean on this branch. The mutable local still contains
  // an object, not the field's saved Boolean: these are distinct snapshots.
  must(
    entry.bindings.find((b) => b.name === "cell"),
    "cell",
  ).type = [1, 2];
  const changed = work + "/claims";
  fs.writeFileSync(changed, JSON.stringify(doc));
  for (const action of ["produce", "check"]) {
    fs.writeFileSync(evidence, original);
    const r = run(action, "source-claims", changed);
    assert.notEqual(
      r.status,
      0,
      "field observation was mistaken for local contents",
    );
  }
  const context = vm.createContext({});
  vm.runInContext(stripTypes(source), context);
  for (const seed of ["true", "false", "null"]) {
    assert.equal(
      vm.runInContext(`checkedMutableObjectReplacement(${seed})`, context),
      false,
    );
    assert.equal(vm.runInContext(`nestedSavedReads(${seed})`, context), false);
  }
  console.log(
    "Inferred replacement: both producers and consumers, distinct local/field observations and later replacement passed",
  );
} finally {
  fs.rmSync(work, { recursive: true, force: true });
}
