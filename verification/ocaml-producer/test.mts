import assert from "node:assert/strict";
import { readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { createHash } from "node:crypto";
import { resolve } from "node:path";
import { openText, definedClassCallables, close as closeParser } from "../tools/fragment-parse.mts";
import { moduleEdges } from "../tools/module-deps.mts";
import { resolveNamedImports, type ModuleSource } from "../tools/module-resolve.mts";
import { spawnSync } from "node:child_process";
import { check, verifier } from "./check.mts";
import { cases } from "./cases.mts";
import type { SourceClaims } from "../tools/source-claims.mts";
import { readDiagnostic } from "../tools/diagnostic.mts";
import { checkGenericRest } from "./generic-rest.mts";
import { checkOverloads } from "./overload-claims.mts";
import { checkDefaults, checkSchemeDefaults, checkEarlyDefault } from "./default-parameters.mts";
// The reader's collector, imported rather than served: `serve.mts` takes the
// port only when it is run directly.
import { analyse } from "../report-viewer/serve.mts";
const here = import.meta.dirname;
// The framework fixture is the upstream source, including its imports and
// classes. A simplified replacement must not quietly inherit its census row.
for (const [file, expected] of [
  ["examples/reactive-sum-prettier-ignore.ts", "f6463ff031d46252cc2a1442c022ea3d709758233e91607eec9673595ea9e271"],
  ["upstream/skipruntime-ts/api-prettier-ignore.ts", "3bfa83b7c2328f4adda5f0bb54569a46c0d776d93184fdb5eb0e789f4b190909"],
  ["upstream/skipruntime-ts/core/src/index-prettier-ignore.ts", "bebd40823a41907ade68b39f755bbceeea5d2afd6ccaaca519e7b6f51ee5586b"],
  ["upstream/skipruntime-ts/core/src/errors-prettier-ignore.ts", "37d2dc3269d9b9ffdd27f50718b5167549e4050edcbbf24491cc477af91c1d27"],
  ["upstream/skipruntime-ts/server/src/server-prettier-ignore.ts", "4a438a5801ff5e99db09b3006971df36e086b0c3da3a358052c79c5fa665458e"],
  ["upstream/skipruntime-ts/core/package-prettier-ignore.json", "edf6f423e4ead592191f34bd14a563014b5afe73568fc15644f624ff0e4e4e54"],
  ["upstream/skipruntime-ts/server/package-prettier-ignore.json", "22a88f9e8400004fecd6e2b05d4d4f3397e727b92445efdbb96e79315754052a"],
] as const) {
  assert.equal(createHash("sha256").update(readFileSync(join(here, file))).digest("hex"), expected,
    `${file}: update the upstream provenance and census before replacing this fixture`);
}
{
  const source = resolve(here, "examples/reactive-sum-prettier-ignore.ts");
  assert.deepEqual(definedClassCallables(source).map(c => c.name), [
    "AddIndex.constructor", "AddIndex.mapEntry", "Plus.mapEntry",
    "Minus.mapEntry", "Add.instantiate", "Sub.instantiate",
  ]);
  const edges = moduleEdges(openText(source, readFileSync(source, "utf8")));
  assert.deepEqual(edges.map(({ specifier, imported, typeOnly }) =>
    [specifier, imported, typeOnly]), [
    ["@skipruntime/core", "EagerCollection", true],
    ["@skipruntime/core", "Mapper", true],
    ["@skipruntime/core", "Resource", true],
    ["@skipruntime/core", "Values", true],
    ["@skipruntime/server", "runService", false],
  ]);
  const api = resolve(here, "upstream/skipruntime-ts/api-prettier-ignore.ts");
  const transitive = moduleEdges(openText(api, readFileSync(api, "utf8")));
  assert(transitive.some((e) => e.kind === "import" && e.imported === "Json" && e.typeOnly));
  assert(transitive.some((e) => e.kind === "reexport" && e.imported === "deepFreeze" && !e.typeOnly));
  const module = (id: string, fixture: string): ModuleSource => {
    const path = resolve(here, "upstream/skipruntime-ts", fixture);
    const bytes = readFileSync(path, "utf8");
    return { id, sha256: createHash("sha256").update(bytes).digest("hex"),
      source: openText(path, bytes) };
  };
  const modules = [
    module("core/src/index.ts", "core/src/index-prettier-ignore.ts"),
    module("core/src/api.ts", "api-prettier-ignore.ts"),
    module("core/src/errors.ts", "core/src/errors-prettier-ignore.ts"),
    module("server/src/server.ts", "server/src/server-prettier-ignore.ts"),
  ];
  const packages = new Map([
    ["@skipruntime/core", "core/src/index.ts"],
    ["@skipruntime/server", "server/src/server.ts"],
  ]);
  for (const [name, file, entry] of [
    ["@skipruntime/core", "core/package-prettier-ignore.json", "./dist/src/index.js"],
    ["@skipruntime/server", "server/package-prettier-ignore.json", "./dist/src/server.js"],
  ]) {
    const data: unknown = JSON.parse(readFileSync(resolve(here, "upstream/skipruntime-ts", file), "utf8"));
    assert.ok(data && typeof data === "object" && "name" in data &&
      "exports" in data && data.exports && typeof data.exports === "object" &&
      "." in data.exports);
    assert.equal(data.name, name);
    assert.equal(data.exports["."], entry);
  }
  const resolved = resolveNamedImports(openText(source, readFileSync(source, "utf8")),
    modules, packages);
  assert.deepEqual(resolved.map(r => [r.binding.local, r.declaration.module,
    r.declaration.name, r.declaration.capability, r.route.map(m => m.module)]), [
    ["EagerCollection", "core/src/api.ts", "EagerCollection", "type",
      ["core/src/index.ts", "core/src/api.ts"]],
    ["Mapper", "core/src/api.ts", "Mapper", "type",
      ["core/src/index.ts", "core/src/api.ts"]],
    ["Resource", "core/src/api.ts", "Resource", "type",
      ["core/src/index.ts", "core/src/api.ts"]],
    ["Values", "core/src/api.ts", "Values", "type",
      ["core/src/index.ts", "core/src/api.ts"]],
    ["runService", "server/src/server.ts", "runService", "value",
      ["server/src/server.ts"]],
  ]);
  assert.throws(() => resolveNamedImports(openText(source, readFileSync(source, "utf8")),
    modules.slice(0, 2), packages), /module not supplied/);
  assert.throws(() => resolveNamedImports(openText(source, readFileSync(source, "utf8")),
    [{ ...modules[0], sha256: "0".repeat(64) }, ...modules.slice(1)], packages),
    /fingerprint differs/);
  const duplicate = "export interface Mapper {}\n";
  assert.throws(() => resolveNamedImports(openText(source, readFileSync(source, "utf8")),
    [...modules.slice(0, 2), {
      id: "core/src/errors.ts",
      sha256: createHash("sha256").update(duplicate).digest("hex"),
      source: openText(resolve(here, "duplicate-errors.ts"), duplicate),
    }, modules[3]], packages), /ambiguous export core\/src\/index.ts#Mapper/);
  const broken = "export { Mapper } from './empty.js';\n";
  const empty = "export const other = 1;\n";
  assert.throws(() => resolveNamedImports(openText(source, readFileSync(source, "utf8")),
    [...modules.slice(0, 2), {
      id: "core/src/errors.ts",
      sha256: createHash("sha256").update(broken).digest("hex"),
      source: openText(resolve(here, "broken-errors.ts"), broken),
    }, modules[3], {
      id: "core/src/empty.ts",
      sha256: createHash("sha256").update(empty).digest("hex"),
      source: openText(resolve(here, "empty.ts"), empty),
    }], packages), /broken named reexport core\/src\/errors.ts#Mapper/);
  closeParser();
}
function must<T>(value: T | null | undefined, message: string): T {
  assert.ok(value !== null && value !== undefined, message);
  return value;
}
let good = "";
let generic = "";
let genericClosure = "";
let twoCalls = "";
let bounded = "";
let returned = "";
let captured = "";
let callback = "";
let inference = "";
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
  if (test.file === "generic-rest") checkGenericRest(verifier, result.artifacts);
  if (test.file === "overloads") checkOverloads(verifier, result.artifacts);
  if (test.file === "values") good = result.artifacts;
  if (test.file === "default-parameter-scope") checkDefaults(verifier, result.artifacts);
  if (test.file === "invalid-default-invocation") checkEarlyDefault(verifier, result.artifacts);
  if (test.file === "generic-default") checkSchemeDefaults(verifier, result.artifacts);
  if (test.file === "generic-inferred") generic = result.artifacts;
  if (test.file === "generic-closure") genericClosure = result.artifacts;
  if (test.file === "generic-two-calls") twoCalls = result.artifacts;
  if (test.file === "generic-bounded") bounded = result.artifacts;
  if (test.file === "generic-returned") returned = result.artifacts;
  if (test.file === "generic-captured-store") captured = result.artifacts;
  if (test.file === "generic-callback") callback = result.artifacts;
  if (test.file === "generic-inference") inference = result.artifacts;
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
  // Returned so a caller can assert the refusal is for the intended reason,
  // not merely that something refused.
  return p.stdout + p.stderr;
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
// narrower first-occurrence proposal after inference has joined both arguments.
{
  const claims: SourceClaims = JSON.parse(readFileSync(join(inference, "claims.json"), "utf8"));
  const joined = must(claims.functions.find(f => f.name === "joinedArguments"), "joined arguments");
  const call = must(joined.expressions.find(e => e.instantiate), "inferred call");
  assert.deepEqual(call.instantiate, [{name: "T", type: [1, 2]}]);
  const upper = must(claims.functions.find(f => f.name === "callbackUpperBounds"), "upper bounds");
  assert.deepEqual(must(upper.expressions.find(e => e.instantiate), "upper call").instantiate,
    [{name: "T", type: [1]}]);
  must(must(call.instantiate, "substitution")[0], "type argument").type = [1];
  call.type = [1];
  const file = join(inference, "forged-first-candidate.json");
  writeFileSync(file, JSON.stringify(claims));
  invoke(file, join(inference, "evidence.json"), inference);
  process.stdout.write("tampered joined inference candidate: refused\n");
}

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
    must(s[0], "the inferred type argument").type = [1, 2];
  }],
  ["substitution domain", (s: NonNullable<typeof sites[1]["instantiate"]>) => {
    must(s[0], "the inferred type argument").name = "U";
  }],
] as const) {
  const claims = structuredClone(twoCallClaims);
  const forged = must(claims.functions[0], "the containing function").expressions.filter((e) => e.instantiate);
  mutate(must(must(forged[1], "the second call").instantiate, "the second substitution"));
  const file = join(twoCalls, `forged-${name.replace(/ /g, "-")}.json`);
  writeFileSync(file, JSON.stringify(claims));
  invoke(file, join(twoCalls, "evidence.json"), twoCalls);
  process.stdout.write(`tampered ${name}: refused\n`);
}

// A substitution is checked against every declared bound before it is
// compiled. Reversing one call's type arguments keeps them ground and complete,
// so the domain check passes and only the bound obligation can refuse it.
const boundedClaims: SourceClaims = JSON.parse(
  readFileSync(join(bounded, "claims.json"), "utf8"),
);
{
  const claims = structuredClone(boundedClaims);
  const call = must(claims.functions[0], "the containing function").expressions.find((e) => e.instantiate);
  assert.ok(call?.instantiate);
  const [u, t] = call.instantiate;
  assert.ok(u && t && u.name === "U" && t.name === "T");
  u.type = [1];
  t.type = [1, 2];
  const file = join(bounded, "forged-bound.json");
  writeFileSync(file, JSON.stringify(claims));
  const said = invoke(file, join(bounded, "evidence.json"), bounded);
  assert.match(said, /does not satisfy the closure's bound: cannot establish boolean ≤ true/);
  process.stdout.write("tampered substituted bound: refused\n");
}

// A nested closure's claim is the type the compiled graph will use for it, so
// introduction requires it to be exactly the source annotation `() => T`: a
// ground `() => boolean` claim fits every observed call and is still refused.
// And a callable over the binder is meaningful only inside its closure: the
// same claim placed on an expression outside it is refused as an escape.
const returnedClaims: SourceClaims = JSON.parse(
  readFileSync(join(returned, "claims.json"), "utf8"),
);
{
  const fn = must(returnedClaims.functions[0], "the containing function");
  const nested = fn.expressions.find(
    (e) => !Array.isArray(e.type) && "scheme" in e.type && e.type.scheme.typeParams.length === 0,
  );
  assert.ok(nested && !Array.isArray(nested.type) && "scheme" in nested.type);
  const outer = fn.expressions.find(
    (e) => !Array.isArray(e.type) && "scheme" in e.type && e.type.scheme.typeParams.length > 0,
  );
  assert.ok(outer && !Array.isArray(outer.type) && "scheme" in outer.type);
  const grounded = structuredClone(returnedClaims);
  const g = must(grounded.functions[0], "the containing function").expressions.find((e) => e.pos[0] === nested.pos[0] && e.pos[1] === nested.pos[1]);
  assert.ok(g && !Array.isArray(g.type) && "scheme" in g.type);
  g.type.scheme.result = [1, 2];
  const groundedFile = join(returned, "forged-nested-claim.json");
  writeFileSync(groundedFile, JSON.stringify(grounded));
  assert.match(invoke(groundedFile, join(returned, "evidence.json"), returned),
    /nested closure claim differs from its source annotation/);
  process.stdout.write("tampered nested closure claim: refused\n");

  const escaped = structuredClone(returnedClaims);
  const outside = must(escaped.functions[0], "the containing function").expressions.find(
    (e) => e.pos[0] > outer.pos[1] && Array.isArray(e.type),
  );
  assert.ok(outside, "an expression after the closure");
  outside.type = nested.type;
  const escapedFile = join(returned, "forged-escape.json");
  writeFileSync(escapedFile, JSON.stringify(escaped));
  assert.match(invoke(escapedFile, join(returned, "evidence.json"), returned),
    /escapes its closure/);
  process.stdout.write("tampered rigid callable escape: refused\n");
}

// A captured cell keeps the contract its declaration states. Retyping it in the
// entry claim the closure is checked against changes what the body reads, so
// the scheme's own body check refuses: a capture is never retyped per call.
const capturedClaims: SourceClaims = JSON.parse(
  readFileSync(join(captured, "claims.json"), "utf8"),
);
{
  const claims = structuredClone(capturedClaims);
  const fn = must(claims.functions[0], "the containing function");
  const declaration = fn.entries.find((e) => e.bindings.some((b) => b.name === "store") && !e.bindings.some((b) => b.name === "read"));
  assert.ok(declaration, "the entry at the closure's declaration");
  const store = declaration.bindings.find((b) => b.name === "store");
  assert.ok(store);
  store.type = [1, 2];
  const file = join(captured, "forged-capture.json");
  writeFileSync(file, JSON.stringify(claims));
  assert.match(invoke(file, join(captured, "evidence.json"), captured),
    /does not satisfy its scheme universally: cannot establish boolean ≤ number/);
  process.stdout.write("tampered captured cell contract: refused\n");
}

// A substitution proposed through a callback is validated like any other:
// naming `number` for the call whose value is `flag` yields a genuine instance
// of the scheme whose value parameter the argument then fails to meet.
const callbackClaims: SourceClaims = JSON.parse(
  readFileSync(join(callback, "claims.json"), "utf8"),
);
{
  const claims = structuredClone(callbackClaims);
  const fn = claims.functions.find((f) => f.name === "throughCallback");
  assert.ok(fn);
  const site = fn.expressions.find((e) => e.instantiate?.some((i) => Array.isArray(i.type) && i.type.length === 2));
  assert.ok(site?.instantiate, "the call instantiated at boolean");
  must(site.instantiate[0], "the callback substitution").type = [4];
  const file = join(callback, "forged-callback-instance.json");
  writeFileSync(file, JSON.stringify(claims));
  invoke(file, join(callback, "evidence.json"), callback);
  process.stdout.write("tampered callback instantiation: refused\n");
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
  assert.match(p.stdout + p.stderr, /generic (entry claim|expression claim|binding annotation|return contract) at \[\d+,\d+\): cannot establish/);
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
{
  const shown = await analyse(repositoryPath("generic-default"), "ocaml");
  const results = shown.manifest.results ?? [];
  assert.deepEqual(results.map((r) => r.status), ["not-established"]);
  assert.notEqual(results[0]?.location, undefined);
  assert.match(JSON.stringify(results), /body requires a variable, a primitive literal, an assignment, a call or a closure/);
  process.stdout.write("reader collection: uncertified scheme defaults visibly refused\n");
}
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

const collectedDefaults = await analyse(repositoryPath("generic-rigid-default"), "ocaml");
assert.equal(collectedDefaults.collection?.verified, true);
assert.match(
  collectedDefaults.manifest.functions[0]?.expressions.find(e => e.type.startsWith("<"))?.type ?? "",
  /arg1: \(T\) \| \(undefined\)/,
);
process.stdout.write("reader collection: rigid default union rendered\n");


const collectedRest = await analyse(repositoryPath("generic-rest"), "ocaml");
assert.equal(collectedRest.collection?.verified, true);
assert.match(collectedRest.manifest.functions.find(f=>f.name === "genericRestUses")?.expressions
  .find(e=>e.type.startsWith("<"))?.type ?? "", /^<T>\(\.\.\.rest: Array<T>\) => Array<T>$/);
process.stdout.write("reader collection: quantified rest and array contracts rendered\n");

// A negative control must reach validation and fail there. Failing there means
// failing an obligation, which the reader can show at its span; an adapter that
// throws before any obligation exists has refused, not validated, and the
// reader can point at nothing. Ranging over the inventory is what keeps a new
// control from escaping this.
const directControls = new Set([
  "invalid-generic-rest",
  "invalid-generic-rest-argument",
  "invalid-generic",
  "invalid-generic-copy",
  "invalid-generic-closure",
  "invalid-scheme-capture",
  "invalid-generic-default",
  "invalid-rigid-default",
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
      // Deliberately outside the typed union: the reader must refuse it at run time.
      // Reflect keeps this malformed-wire test from weakening the typed source.
      Reflect.set(unknown.judgment, "kind", "future-judgment");
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
