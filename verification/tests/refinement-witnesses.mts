import assert from "node:assert/strict";
import fs from "node:fs";
import path from "node:path";
import os from "node:os";
import { spawnSync } from "node:child_process";
import { readDiagnostic } from "../tools/obligation-diagnostic.mts";
const __dirname = path.dirname(import.meta.filename);
// The original exports must fail only at the stale observation. Controls differ
// solely by removal of the invalidating operation, and use fresh producer claims.






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
const load = (p) => JSON.parse(fs.readFileSync(p, "utf8"));
const run = (exe, args, cwd = root) => {
  const r = spawnSync(exe, args, {
    cwd,
    encoding: "utf8",
    timeout: 60000,
    maxBuffer: 8 * 1024 * 1024,
  });
  assert(!r.error && !r.signal, String(r.error || r.signal));
  return r;
};
const strip = (x) =>
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
function test(name, f) {
  f();
  passed++;
  console.log(`  ${name}: OK`);
}
try {
  const controls = load(controlAst).functions;
  for (const [ap, cp, file] of [
    [capturedAst, capturedClaims, capturedFile],
    [compoundAst, compoundClaims, compoundFile],
  ]) {
    const ast = load(ap),
      raw = load(cp);
    test("every original obligation audited in " + path.basename(file), () => {
      const r = run(
        "lake",
        [
          "env",
          "lean",
          "--run",
          path.join(__dirname, "witness-audit.lean"),
          ap,
          cp,
          file,
        ],
        path.join(root, "verification/lean"),
      );
      assert.equal(r.status, 0, r.stdout + r.stderr);
      process.stdout.write(r.stdout);
    });
    for (const f of ast.functions) {
      const target = f.name.replace("stale", "stable");
      const expected = strip(f);
      expected.name = target;
      if (f.name === "staleCapturedCell")
        expected.body[2].then[0].init = { k: "lit", lit: { a: "null" } };
      else expected.body[1].body.shift();
      test(`${f.name}: control retains the exact guard and read`, () =>
        assert.deepEqual(
          strip(controls.find((c) => c.name === target)),
          expected,
        ));
      const arm =
        f.name === "staleCapturedCell" ? f.body[2].then : f.body[1].body;
      const ret = arm.at(-1);
      const a = { ...ast, functions: [f] },
        c = structuredClone(raw);
      c.find((x) => x.file === file).functions = c
        .find((x) => x.file === file)
        .functions.filter((x) => x.name === f.name);
      const ax = path.join(tmp, "ast.json"),
        cx = path.join(tmp, "raw.json"),
        sx = path.join(tmp, "sidecar.json"),
        ep = path.join(tmp, "evidence.json");
      fs.writeFileSync(ax, JSON.stringify(a));
      fs.writeFileSync(cx, JSON.stringify(c));
      const converted = run(verifier, ["--export-source-claims", ax, cx, file]);
      assert.equal(converted.status, 0, converted.stderr);
      fs.writeFileSync(sx, JSON.stringify(JSON.parse(converted.stdout).claims));
      for (const [mode, claims] of [
        ["stateful-source", cx],
        ["source-claims", sx],
      ])
        test(`${f.name}: ${mode} locates the post-mutation assertion`, () => {
          const r = run(verifier, [
            "--produce-" + mode,
            ax,
            claims,
            file,
            ep,
            "10",
          ]);
          assert.notEqual(r.status, 0);
          const d = readDiagnostic(r.stderr);
          assert(d, r.stderr);
          assert.equal(d.phase, "proof-search");
          assert.equal(d.kind, "edge-coverage");
          assert.equal(d.destination.sourceMap.role, "heap-observation");
          assert.equal(d.destination.sourceMap.environmentStart, ret.pos[0]);
          assert.deepEqual(d.destination.sourceMap.pos, ret.pos);
          const literal = f.name === "staleFlip" ? "fls" : "tru";
          assert(
            d.destination.requiredKnowledge.cells.some(
              (x) => String(x.contents) === literal,
            ),
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
