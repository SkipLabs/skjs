import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { spawnSync } from "node:child_process";
const __dirname = path.dirname(import.meta.filename);
// What TypeScript's own checker believes, put through the verifier.
//
// `tools/tsc-claims.mts` states tsc's types at every site of a corpus file as a
// producer-neutral claims document; this runs that over the corpus and records
// the verdict per file. The expected verdicts below are policy, the same shape
// as `expectedVerified` in examples.mts: a change here is a change in what one
// checker's claims can be derived from, to be read rather than regenerated.




const verifier = process.argv[2];
if (!verifier) throw Error("usage: tsc-claims.mts <verifier>");
const root = path.resolve(__dirname, "../..");
process.chdir(root);
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "tsc-claims-"));

// Why each file lands where it does. A verified file says tsc's claims are
// derivable in the calculus; a failing one names what stops them.
const expected = {
  // tsc's flow narrowing carries these, where SKJS's own claims needed a
  // hand repair at the loop exit or the negation.
  "stateful-source/basic": "verified",
  "stateful-source/cells": "verified",
  "stateful-source/cell-conjunction": "verified",
  "stateful-source/closures": "verified",
  "stateful-source/loops": "verified",
  "stateful-source/loop-transfers": "verified",
  "stateful-source/negation": "verified",
  "stateful-source/null-tests": "verified",
  "stateful-source/undefined": "verified",
  "skjs-incomplete/negated-loop-exit": "verified",
  "skjs-incomplete/null-loop-exit": "verified",
  "skjs-incomplete/singleton-negation": "verified",
  "skjs-incomplete/undefined-completes": "verified",
  "skjs-incomplete/arrow-intersection": "verified",
  // A cell read after a write is true at runtime and tsc types it so; the
  // calculus reads a cell at its invariant unless the point carries a
  // current-content assertion, which this producer does not write.
  "skjs-incomplete/write-refined-read": "failed",
  "stateful-source/primitive-callbacks": "failed",
  // A closure claimed at a union of an arrow and null: the adapter's lambda
  // rule takes a single arrow row.
  "stateful-source/null-guards": "failed",
  // tsc rejects these outright, so its claims describe a program it does not
  // accept; the verifier refusing them says nothing about either checker.
  "skjs-incomplete/empty-domain-escape": "failed",
  "skjs-unsound/never-completes": "failed",
  "skjs-unsound/compound-write-refinement": "failed",
  "skjs-unsound/arrow-intersection": "failed",
  // The finding: tsc accepts this with no diagnostic, and the verifier cannot
  // derive its claim for the read after the callback wrote the cell. The
  // function returns false where it declares true.
  "skjs-unsound/captured-refinement": "failed",
  // A cell parameter with a non-mutable field: outside the source fragment.
  "stateful-source/cell-contracts": "out-of-fragment",
};

const run = (cmd, args) =>
  spawnSync(cmd, args, { encoding: "utf8", timeout: 120000 });
let failures = 0;
for (const [name, want] of Object.entries(expected)) {
  const file = `verification/tests/${name}.ts`;
  const ast = path.join(tmp, "ast.json"),
    claims = path.join(tmp, "claims.json"),
    evidence = path.join(tmp, "evidence.json");
  let got, detail = "";
  const parsed = run(process.execPath, [
    "verification/tools/parse-source.mts",
    file,
  ]);
  if (parsed.status !== 0) {
    got = "out-of-fragment";
    detail = (parsed.stderr || "").split("\n")[0];
  } else {
    fs.writeFileSync(ast, parsed.stdout);
    const produced = run(process.execPath, [
      "verification/tools/tsc-claims.mts",
      file,
      "--out",
      claims,
    ]);
    if (produced.status !== 0) {
      got = "producer-error";
      detail = (produced.stderr || "").split("\n")[0];
    } else {
      const checked = run(verifier, [
        "--produce-source-claims",
        ast,
        claims,
        file,
        evidence,
        "10",
      ]);
      got = checked.status === 0 ? "verified" : "failed";
      if (got === "failed")
        detail = (checked.stderr || "").split("\n")[0].replace(/^reject: /, "");
    }
  }
  if (got === want) {
    console.log(`  ${name}: ${got}${detail ? ` — ${detail.slice(0, 60)}` : ""}`);
  } else {
    failures++;
    console.log(`  ${name}: expected ${want}, got ${got} — ${detail}`);
  }
}
fs.rmSync(tmp, { recursive: true, force: true });
const total = Object.keys(expected).length;
console.log(
  `TypeScript claims: ${total - failures} as expected, ${failures} changed`,
);
process.exit(failures ? 1 : 0);
