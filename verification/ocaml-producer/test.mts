import assert from "node:assert/strict";
import { readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { spawnSync } from "node:child_process";
import { check, verifier } from "./check.mts";
import type { SourceClaims } from "../tools/source-claims.mts";
const here = import.meta.dirname;
const outcomes = [
  ["values", "verified"],
  ["branches", "verified"],
  ["objects", "verified"],
  ["callbacks", "verified"],
  ["generics", "verified"],
  ["generic-inferred", "unverified"],
  ["invalid-return", "unverified"],
  ["invalid-local-write", "unverified"],
  ["invalid-callback", "unverified"],
  ["invalid-variance", "unverified"],
  ["invalid-write", "unverified"],
  ["invalid-capture", "unverified"],
  ["invalid-generic", "unverified"],
  ["unsupported", "unsupported"],
];
let good = "";
for (const [name, expected] of outcomes) {
  const result = check(join(here, "examples", `${name}.ts`));
  assert.equal(result.status, expected, `${name}: ${JSON.stringify(result)}`);
  process.stdout.write(`${name}: ${result.status}\n`);
  if (name === "values") good = result.artifacts;
}
// Mutations work on the shared typed wire document. JSON is first checked by
// Lean above; no second hand-maintained SourceClaims shape is introduced here.
const original: SourceClaims = JSON.parse(
  readFileSync(join(good, "claims.json"), "utf8"),
);
const invoke = (claims: string, evidence: string) => {
  const p = spawnSync(
    verifier,
    [
      "--check-source-claims",
      join(good, "fragment.json"),
      claims,
      join(good, "source.ts"),
      evidence,
    ],
    { encoding: "utf8", timeout: 30_000 },
  );
  assert.ifError(p.error);
  assert.equal(p.signal, null);
  assert.equal(p.status, 1, p.stdout + p.stderr);
};
for (const [name, mutate] of new Map<string, (c: SourceClaims) => void>([
  [
    "fingerprint",
    (c) => {
      c.sourceSha256 = "0".repeat(64);
    },
  ],
  [
    "missing-function",
    (c) => {
      c.functions.pop();
    },
  ],
  [
    "false-expression",
    (c) => {
      const e = c.functions[0]?.expressions[0];
      assert.ok(e);
      e.type = [0];
    },
  ],
])) {
  const c = structuredClone(original);
  mutate(c);
  const path = join(good, `${name}.json`);
  writeFileSync(path, JSON.stringify(c));
  invoke(path, join(good, "evidence.json"));
  process.stdout.write(`tampered ${name}: refused\n`);
}
const badEvidence = join(good, "bad-evidence.json");
writeFileSync(badEvidence, "{}");
invoke(join(good, "claims.json"), badEvidence);
process.stdout.write("tampered evidence: refused\n");
