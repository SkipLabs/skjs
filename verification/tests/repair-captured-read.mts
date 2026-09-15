import assert from "node:assert/strict";
import fs from "node:fs";
import { spawnSync } from "node:child_process";
import { parseFile, close } from "../tools/parse-source.mts";
import { extractFunctions } from "../tools/extract-functions.mts";
import { produce } from "../tools/tsc-claims.mts";

// Extract unchanged bodies from the repair tests, not parallel hand-written
// examples. The two stale controls must stay unverified with fresh raw claims.
const original = "tests/expect-error/captured-read-stability.ts";
const groups = {
  accepted: ["checkedAnnotatedConstField", "checkedInferredObject"],
  rejected: ["staleAnnotatedConstField", "inferredObjectCapture"],
};
const [mode, directory, claimsPath, verifier] = process.argv.slice(2);
if (mode === "--extract") {
  fs.writeFileSync(`${directory}/tsconfig.json`, JSON.stringify({
    extends: "../tsconfig.json", include: ["*.ts"],
  }));
  for (const [group, names] of Object.entries(groups)) {
    const file = `${directory}/${group}.ts`;
    fs.writeFileSync(file, extractFunctions(original, names));
    fs.writeFileSync(`${file}.ast`, JSON.stringify(parseFile(file)));
  }
  close();
} else {
  assert.equal(mode, "--check");
  const raw = JSON.parse(fs.readFileSync(claimsPath, "utf8"));
  const attempt = (file: string, ast: any, claims: any, normalized = false) => {
    const ap = `${directory}/attempt.ast`, cp = `${directory}/attempt.claims`;
    const ep = `${directory}/evidence.json`;
    fs.writeFileSync(ap, JSON.stringify(ast));
    fs.writeFileSync(cp, JSON.stringify(claims));
    const format = normalized ? "source-claims" : "stateful-source";
    const r = spawnSync(verifier, [`--produce-${format}`, ap, cp, file, ep, "10"], { encoding: "utf8" });
    if (r.error || r.signal) throw r.error || Error(String(r.signal));
    if (r.status === 0) {
      const checked = spawnSync(verifier, [`--check-${format}`, ap, cp, file, ep], { encoding: "utf8" });
      assert.equal(checked.status, 0, checked.stderr);
    }
    return r;
  };
  for (const [group, names] of Object.entries(groups)) {
    const file = `${directory}/${group}.ts`;
    const ast = JSON.parse(fs.readFileSync(`${file}.ast`, "utf8"));
    const exported = raw.filter((f: any) => f.file === file);
    assert.equal(exported.length, 1);
    const tsc = produce(file);
    for (const name of names) {
      const a = { ...ast, functions: ast.functions.filter((f: any) => f.name === name) };
      const skjs = [{ ...exported[0], functions: exported[0].functions.filter((f: any) => f.name === name) }];
      const t = { ...tsc.doc, functions: tsc.doc.functions.filter(f => f.name === name) };
      assert.equal(skjs[0].functions.length, 1);
      assert.equal(t.functions.length, 1);
      for (const [producer, claims, normalized] of [["SKJS", skjs, false], ["TypeScript", t, true]] as const) {
        const r = attempt(file, a, claims, normalized);
        assert.equal(r.status === 0, group === "accepted", `${name} (${producer}): ${r.stderr}`);
        console.log(`  ${name}: ${producer} ${r.status === 0 ? "verified" : "not established"}`);
      }
    }
    if (group === "accepted") {
      // A write after the guard must disable snapshot reuse. This is a mutated
      // source request with the old claims, so it also checks the trust boundary.
      const changed = structuredClone(ast);
      const findNode = (e: any, kind: string): any => {
        if (!e || typeof e !== "object") return null;
        if (e.k === kind) return e;
        for (const value of Object.values(e)) {
          const found = findNode(value, kind);
          if (found) return found;
        }
        return null;
      };
      const branch = findNode(changed.functions[0], "ifBody");
      assert(branch);
      // Reuse the existing, fully claimed write from after the closure.
      const write = structuredClone(findNode(changed.functions[0], "write"));
      assert(write);
      branch.then = { k: "seqBody", pos: branch.then.pos, init: write, body: branch.then };
      const invalidated = attempt(file, changed, exported);
      assert.notEqual(invalidated.status, 0);
      assert.match(invalidated.stderr, /heap-observation/);
      console.log("  write in guarded branch disables saved-read refinement");
    }
  }
  close();
}
