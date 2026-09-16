import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import vm from "node:vm";
import { spawnSync } from "node:child_process";
import type { Ast } from "../tools/fragment.mts";
import type { SourceClaims } from "../tools/source-claims.mts";
import { stripTypes } from "../tools/strip-types.mts";
import { must } from "./edits.mts";
const [
  astPath,
  claimsPath,
  file,
  controlsAst,
  controlsClaims,
  controlsFile,
  verifier,
] = process.argv.slice(2);
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "mutable-guards-"));
try {
  const proof = path.join(tmp, "proof.json"),
    claim = path.join(tmp, "claims.json");
  const run = (mode: string, a: string, c: string, f: string) => {
    const args = [mode, a, c, f, proof];
    if (mode.startsWith("--produce")) args.push("10");
    const r = spawnSync(verifier, args, { encoding: "utf8" });
    assert(!r.error && !r.signal, String(r.error || r.signal));
    return r;
  };
  for (const mode of ["--produce-stateful-source", "--check-stateful-source"]) {
    const r = run(mode, astPath, claimsPath, file);
    assert.equal(r.status, 0, r.stdout + r.stderr);
  }
  const context = vm.createContext({});
  vm.runInContext(
    stripTypes(fs.readFileSync(file, "utf8")) +
      stripTypes(fs.readFileSync(controlsFile, "utf8")),
    context,
  );
  assert.equal(vm.runInContext("guardedCapturedRead(true)", context), false);
  for (const name of ["writeAfterGuard", "callAfterGuard"])
    assert.equal(vm.runInContext(`${name}(true)`, context), null);
  const ast: Ast = JSON.parse(fs.readFileSync(controlsAst, "utf8"));
  const doc: SourceClaims = JSON.parse(fs.readFileSync(controlsClaims, "utf8"));
  for (const f of ast.functions) {
    const a = { ...ast, functions: [f] };
    const ap = path.join(tmp, "ast.json");
    fs.writeFileSync(ap, JSON.stringify(a));
    const fc = structuredClone(
      must(
        doc.functions.find((c) => c.name === f.name),
        f.name,
      ),
    );
    // Use deliberately broad entry claims so a precise post-write `null`
    // assertion cannot accidentally be what rejects the forged saved read.
    for (const entry of fc.entries)
      for (const binding of entry.bindings)
        if (binding.name === "value") binding.type = [0, 1, 2];
    // Strengthen precisely the final local read in the guarded branch. At
    // runtime the preceding write/call has set this location to null.
    const source = fs.readFileSync(controlsFile, "utf8");
    const reads = fc.expressions.filter(
      (e) => source.slice(...e.pos) === "value",
    );
    const last = must(
      reads.sort((a, b) => b.pos[0] - a.pos[0])[0],
      "branch return read",
    );
    last.type = [1, 2];
    fs.writeFileSync(claim, JSON.stringify({ ...doc, functions: [fc] }));
    const r = run("--produce-source-claims", ap, claim, controlsFile);
    assert.notEqual(r.status, 0, `${f.name}: a guard cannot survive an effect`);
    assert.match(r.stderr, /evidence search failed/);
  }
  console.log(
    "captured-local guard verifies independently; writes and calls cannot reuse its saved read",
  );
} finally {
  fs.rmSync(tmp, { recursive: true, force: true });
}
