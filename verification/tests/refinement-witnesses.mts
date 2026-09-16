import assert from "node:assert/strict";
import fs from "node:fs";
import path from "node:path";
import os from "node:os";
import { spawnSync } from "node:child_process";
import type { Ast } from "../tools/fragment.mts";
import { functionOf, type SkjsClaims } from "../tools/skjs-claims.mts";
import { field, fn, list, must, record } from "./edits.mts";
const __dirname = path.dirname(import.meta.filename);
// Explicit calls and direct writes now reject in SKJS; unchanged controls verify.






const [
  verifier,
  capturedAst,
  capturedClaims,
  capturedFile,
  compoundAst,
  compoundClaims,
  compoundFile,
  controlAst,
  controlClaims,
  controlFile,
] = process.argv.slice(2);
const root = path.resolve(__dirname, "../..");

const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "refinement-witnesses-"));
const load = <T,>(p: string | undefined): T =>
  JSON.parse(fs.readFileSync(must(p, "a path"), "utf8"));
const run = (exe: string, args: string[], cwd = root) => {
  const r = spawnSync(exe, args, {
    cwd,
    encoding: "utf8",
    timeout: 60000,
    maxBuffer: 8 * 1024 * 1024,
  });
  assert(!r.error && !r.signal, String(r.error || r.signal));
  return r;
};
/* Two trees are compared for everything except where they sit, so what is
 * compared is no longer a fragment tree and is not typed as one. */
const strip = (x: unknown): unknown =>
  Array.isArray(x)
    ? x.map(strip)
    : x && typeof x === "object"
      ? Object.fromEntries(
          Object.entries(x)
            .filter(([k]) => !["pos", "namePos"].includes(k))
            .map(([k, v]) => [k, strip(v)]),
        )
      : x;
let passed = 0;
function test(name: string, f: () => void) {
  f();
  passed++;
  console.log(`  ${name}: OK`);
}
try {
  const controls: Ast = load(controlAst);
  for (const [ap, cp, file] of [
    [capturedAst, capturedClaims, capturedFile],
    [compoundAst, compoundClaims, compoundFile],
  ]) {
    const ast: Ast = load(ap);
    const raw: SkjsClaims = load(cp);
    for (const f of ast.functions) {
      const target = f.name.replace("stale", "stable");
      const expected = record(strip(f), "the stripped function");
      expected.name = target;
      if (f.name === "staleCapturedCell")
        record(field(expected, "body", 2, "then", 0), "the guarded binding")
          .init = { k: "lit", lit: { a: "null" } };
      else list(field(expected, "body", 1, "body"), "the loop body").shift();
      test(`${f.name}: control retains the exact guard and read`, () =>
        assert.deepEqual(strip(fn(controls, target)), expected));
      test(`${f.name}: SKJS rejects the stale return`, () => {
        assert.equal(
          functionOf(raw, must(file, "a file key"), f.name).collection?.completion,
          "aborted",
        );
      });
    }
  }
  const sidecar = path.join(tmp, "controls.json"),
    evidence = path.join(tmp, "controls.evidence.json");
  const exported = run(verifier, [
    "--export-source-claims",
    controlAst,
    controlClaims,
    controlFile,
  ]);
  assert.equal(exported.status, 0, exported.stderr);
  fs.writeFileSync(sidecar, JSON.stringify(JSON.parse(exported.stdout).claims));
  for (const [producer, claims, consumer, other] of [
    ["stateful-source", controlClaims, "source-claims", sidecar],
    ["source-claims", sidecar, "stateful-source", controlClaims],
  ])
    test(`all three controls: ${producer} evidence independently checks as ${consumer}`, () => {
      const p = run(verifier, [
        "--produce-" + producer,
        controlAst,
        claims,
        controlFile,
        evidence,
        "10",
      ]);
      assert.equal(p.status, 0, p.stderr);
      const c = run(verifier, [
        "--check-" + consumer,
        controlAst,
        other,
        controlFile,
        evidence,
      ]);
      assert.equal(c.status, 0, c.stderr);
    });
  console.log(`Refinement witness audit: ${passed} passed, 0 failed`);
} finally {
  fs.rmSync(tmp, { recursive: true, force: true });
}
