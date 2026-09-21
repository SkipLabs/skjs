import assert from "node:assert/strict";
import { readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { spawnSync } from "node:child_process";
import { check, verifier } from "./check.mts";
import { cases } from "./cases.mts";
import type { SourceClaims } from "../tools/source-claims.mts";
import { readDiagnostic } from "../tools/diagnostic.mts";
// The reader's collector, imported rather than served: `serve.mts` takes the
// port only when it is run directly.
import { analyse } from "../report-viewer/serve.mts";
const here = import.meta.dirname;
let good = "";
let generic = "";
let genericClosure = "";
let twoCalls = "";
let verifiedFunctions = 0;
for (const test of cases) {
  const result = check(join(here, "examples", `${test.file}.ts`));
  assert.equal(
    result.status,
    test.status,
    `${test.file}: ${JSON.stringify(result)}`,
  );
  assert.equal(result.phase, test.phase, `${test.file}: wrong boundary`);
  if (test.diagnostic) {
    assert.notEqual(result.status, "verified");
    if (result.status !== "verified")
      assert.match(
        result.detail,
        test.diagnostic,
        `${test.file}: wrong failure`,
      );
  }
  if (result.status === "verified")
    verifiedFunctions += result.functions.length;
  process.stdout.write(
    `${test.file}: ${result.status} (${result.phase}, ${test.kind})\n`,
  );
  if (test.file === "values") good = result.artifacts;
  if (test.file === "generic-inferred") generic = result.artifacts;
  if (test.file === "generic-closure") genericClosure = result.artifacts;
  if (test.file === "generic-two-calls") twoCalls = result.artifacts;
}
process.stdout.write(
  `${verifiedFunctions} functions verified; ${cases.filter((c) => c.kind === "negative").length} negative controls; ${cases.filter((c) => c.kind === "gap").length} named gaps\n`,
);
// Mutations work on the shared typed wire document. JSON is first checked by
// Lean above; no second hand-maintained SourceClaims shape is introduced here.
const original: SourceClaims = JSON.parse(
  readFileSync(join(good, "claims.json"), "utf8"),
);
const invoke = (claims: string, evidence: string, artifacts = good) => {
  const p = spawnSync(
    verifier,
    [
      "--check-source-claims",
      join(artifacts, "fragment.json"),
      claims,
      join(artifacts, "source.ts"),
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

// A graph certificate for the checked Boolean instance cannot validate a
// different quantified contract. The scheme itself is independently consumed.
const closureClaims: SourceClaims = JSON.parse(
  readFileSync(join(genericClosure, "claims.json"), "utf8"),
);
const closure = closureClaims.functions[0];
assert.ok(closure);
const schemePoint = closure.expressions.find(
  (e) => !Array.isArray(e.type) && "scheme" in e.type,
);
assert.ok(schemePoint && !Array.isArray(schemePoint.type) && "scheme" in schemePoint.type);
schemePoint.type.scheme.result = [1, 2];
const forgedScheme = join(genericClosure, "forged-scheme.json");
writeFileSync(forgedScheme, JSON.stringify(closureClaims));
invoke(forgedScheme, join(genericClosure, "evidence.json"), genericClosure);
process.stdout.write("tampered quantified closure scheme: refused\n");

// A call's substitution is the elimination it proposes, so evidence produced
// for the checked substitutions cannot certify a different one. Retyping the
// second call's type argument leaves one genuine instance of the same scheme,
// which is why the argument — not the universal gate — is what refuses it.
const twoCallClaims: SourceClaims = JSON.parse(
  readFileSync(join(twoCalls, "claims.json"), "utf8"),
);
const instantiated = twoCallClaims.functions[0];
assert.ok(instantiated);
const sites = instantiated.expressions.filter((e) => e.instantiate);
assert.equal(sites.length, 2, "both eliminations must carry a substitution");
for (const [name, mutate] of [
  ["substitution", (s: NonNullable<typeof sites[1]["instantiate"]>) => {
    s[0]!.type = [1, 2];
  }],
  ["substitution domain", (s: NonNullable<typeof sites[1]["instantiate"]>) => {
    s[0]!.name = "U";
  }],
] as const) {
  const claims = structuredClone(twoCallClaims);
  const forged = claims.functions[0]!.expressions.filter((e) => e.instantiate);
  mutate(forged[1]!.instantiate!);
  const file = join(twoCalls, `forged-${name.replace(/ /g, "-")}.json`);
  writeFileSync(file, JSON.stringify(claims));
  invoke(file, join(twoCalls, "evidence.json"), twoCalls);
  process.stdout.write(`tampered ${name}: refused\n`);
}

// Generic bodies take the rigid-bound path in BOTH producer and consumer.
// Reusing valid evidence must not let an inferred local trust a forged point type.
const genericClaims: SourceClaims = JSON.parse(
  readFileSync(join(generic, "claims.json"), "utf8"),
);
for (const site of ["initializer", "binding"] as const) {
  const claims = structuredClone(genericClaims);
  const fn = claims.functions.find((f) => f.name === "inferred");
  assert.ok(fn);
  if (site === "initializer") {
    const initial = fn.expressions[0];
    assert.ok(initial);
    initial.type = [1, 2];
  } else {
    const saved = fn.entries.flatMap((e) => e.bindings).find((b) => b.name === "saved");
    assert.ok(saved);
    saved.type = [1, 2];
  }
  const file = join(generic, `forged-${site}.json`);
  writeFileSync(file, JSON.stringify(claims));
  const p = spawnSync(verifier, [
    "--check-source-claims", join(generic, "fragment.json"), file,
    join(generic, "source.ts"), join(generic, "evidence.json"),
  ], {encoding: "utf8", timeout: 30_000});
  assert.ifError(p.error);
  assert.equal(p.signal, null);
  assert.equal(p.status, 1, p.stdout + p.stderr);
  assert.match(p.stdout + p.stderr, /generic obligation: cannot establish/);
  assert.match(p.stdout + p.stderr, /"role":"(?:expression|entry)-claim"/);
  process.stdout.write(`tampered inferred generic ${site}: refused\n`);
}

// A malformed direct-check input is a located refusal, not prose disguised as
// a failed judgment. The closed failure sum makes this branch mandatory at the
// Lean boundary, and the reader must preserve the distinction.
{
  const claims = structuredClone(genericClaims);
  const fn = claims.functions.find((f) => f.name === "inferred");
  assert.ok(fn);
  fn.expressions.pop();
  const file = join(generic, "missing-generic-expression.json");
  writeFileSync(file, JSON.stringify(claims));
  const p = spawnSync(verifier, [
    "--check-source-claims", join(generic, "fragment.json"), file,
    join(generic, "source.ts"), join(generic, "evidence.json"),
  ], {encoding:"utf8",timeout:30_000});
  assert.equal(p.status,1,p.stdout+p.stderr);
  const refusal = readDiagnostic(p.stdout+p.stderr);
  assert(refusal?.kind === "source-refusal");
  assert.deepEqual(refusal.sourceMap.pos,fn.namePos);
  assert(!("judgment" in refusal));
  process.stdout.write("malformed generic input: located refusal\n");
}

/*
 * The reader collects this producer too. It runs the same two steps `check`
 * runs — the shared parser, then `producer.exe` over the Fragment — and hands
 * what came out to the same verifier, so what it displays is this producer's
 * own document adjudicated the same way. What is checked here is that
 * correspondence: the claims the reader carries are the ones the producer
 * wrote, the verdicts are the verifier's, and a source this producer does not
 * implement is refused in its own words rather than collected as an empty
 * report.
 */
const repositoryPath = (file: string) =>
  `verification/ocaml-producer/examples/${file}.ts`;
const collected = await analyse(repositoryPath("values"), "ocaml");
assert.equal(collected.collection?.producer, "ocaml");
assert.equal(collected.collection?.producerRun, true);
assert.equal(collected.collection?.verified, true);
assert.equal(collected.candidate?.format, "source-claims");
// The document the reader offers for editing is the producer's own, not a
// display shape derived from it: the same bytes `check` wrote beside `values`.
assert.deepEqual(collected.candidate?.claims, {
  ...original,
  file: repositoryPath("values"),
});
assert.deepEqual(
  (collected.manifest.results ?? []).map((r) => r.status),
  ["verified", "verified"],
);
process.stdout.write(
  `reader collection: ${collected.manifest.functions.length} functions, producer's own claims verified\n`,
);

const collectedGeneric = await analyse(
  repositoryPath("generic-closure"),
  "ocaml",
);
assert.equal(collectedGeneric.collection?.verified, true);
assert.equal(collectedGeneric.candidate?.format, "source-claims");
assert.match(
  collectedGeneric.manifest.functions[0]?.expressions.find((e) =>
    e.type.startsWith("<"),
  )?.type ?? "",
  /^<T>\(arg0: T\) => T$/,
);
process.stdout.write("reader collection: quantified callable rendered\n");

// A negative control must reach validation and fail there. Failing there means
// failing an obligation, which the reader can show at its span; an adapter that
// throws before any obligation exists has refused, not validated, and the
// reader can point at nothing. Ranging over the inventory is what keeps a new
// control from escaping this.
const directControls = new Set([
  "invalid-generic",
  "invalid-generic-copy",
  "invalid-generic-closure",
  "invalid-scheme-capture",
]);
let testedDirectProtocol = false;
for (const control of cases.filter((c) => c.kind === "negative")) {
  const shown = await analyse(repositoryPath(control.file), "ocaml");
  const results = shown.manifest.results ?? [];
  assert.deepEqual(
    results.map((r) => r.status),
    ["not-established"],
    `${control.file}: reader must show it as not established`,
  );
  assert.notEqual(
    results[0]?.location,
    undefined,
    `${control.file}: reached no obligation, so the reader has nothing to show`,
  );
  if (directControls.has(control.file)) {
    assert.equal(
      results[0]?.obligation?.kind,
      "direct-obligation",
      `${control.file}: a direct checker failure needs a structured judgment`,
    );
    const direct = results[0]?.obligation;
    assert(direct?.kind === "direct-obligation");
    assert(!("statement" in direct.judgment), "direct judgments cannot store prose");
    const judgmentView = results[0]?.obligationView?.judgement;
    assert(judgmentView && !("text" in judgmentView),
      "judgment text must be derived by the shared printer");
    if (!testedDirectProtocol) {
      testedDirectProtocol = true;
      const {input: _input, ...wire} = direct;
      const line = (value: unknown) =>
        `obligation-diagnostic: ${JSON.stringify(value)}`;
      assert(readDiagnostic(line(wire)), "the structured direct judgment decodes");
      const unknown = structuredClone(wire);
      unknown.judgment.kind = "future-judgment";
      assert.equal(readDiagnostic(line(unknown)),undefined,"an unhandled judgment variant is refused");
      const unscoped = structuredClone(wire);
      unscoped.judgment.actual = {kind:"rigid",name:"Undeclared"};
      assert.equal(readDiagnostic(line(unscoped)),undefined,"an undeclared rigid type is refused");
      const misplaced = structuredClone(wire);
      misplaced.sourceMap.pos = [0,0];
      assert.equal(readDiagnostic(line(misplaced)),undefined,"a judgment cannot borrow another source span");
    }
  }
}
process.stdout.write(
  `reader collection: ${cases.filter((c) => c.kind === "negative").length} negative controls failed an obligation\n`,
);

// What this producer does not implement is refused where it is refused, in the
// words that boundary uses. It does not become a report with nothing in it.
for (const [file, says] of [
  ["unsupported", /OCaml producer proposed no claims: unsupported:/],
] as const) {
  await assert.rejects(analyse(repositoryPath(file), "ocaml"), says);
  process.stdout.write(`reader collection: ${file} refused by name\n`);
}
