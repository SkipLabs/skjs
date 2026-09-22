import assert from "node:assert/strict";
import { readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { spawnSync } from "node:child_process";
import vm from "node:vm";
import type { Ast } from "../tools/fragment.mts";
import type { SourceClaims } from "../tools/source-claims.mts";
import { stripTypes } from "../tools/strip-types.mts";
import { readDiagnostic } from "../tools/diagnostic.mts";

/** The producer's refusal is not the verifier's protection. Forge a claim for
 * the later read and require both Lean entry points to reject its scope. */
export function checkDefaults(verifier: string, artifacts: string): void {
  const source = join(artifacts, "source.ts");
  const ast: Ast = JSON.parse(
    readFileSync(join(artifacts, "fragment.json"), "utf8"),
  );
  const claims: SourceClaims = JSON.parse(
    readFileSync(join(artifacts, "claims.json"), "utf8"),
  );
  const first = ast.functions[0]?.body[0];
  assert(first?.k === "const");
  const lambda = first.bindings[0]?.init;
  assert(lambda?.k === "lambda");
  const param = lambda.params[0];
  assert(param?.default);
  const pos = param.default.pos;
  param.default = { k: "id", pos, name: "second" };
  const point = claims.functions[0]?.expressions.find(
    (e) => e.pos[0] === pos[0] && e.pos[1] === pos[1],
  );
  assert(point);
  point.type = [1, 2, 3]; // boolean | undefined, the later parameter's type.
  const badAst = join(artifacts, "later-default-ast.json");
  const badClaims = join(artifacts, "later-default-claims.json");
  writeFileSync(badAst, JSON.stringify(ast));
  writeFileSync(badClaims, JSON.stringify(claims));
  for (const mode of ["--produce-source-claims", "--check-source-claims"]) {
    const result = spawnSync(
      verifier,
      [
        mode,
        badAst,
        badClaims,
        source,
        join(artifacts, "evidence.json"),
        ...(mode === "--produce-source-claims" ? ["12"] : []),
      ],
      { encoding: "utf8", timeout: 30_000 },
    );
    assert.ifError(result.error);
    assert.equal(result.signal, null);
    assert.equal(result.status, 1);
    assert.match(
      result.stdout + result.stderr,
      /parameter default may only read initialized earlier parameters/,
    );
  }

  const examples = join(import.meta.dirname, "examples");
  const execute = (file: string, expression: string) =>
    vm.runInNewContext(
      stripTypes(readFileSync(join(examples, `${file}.ts`), "utf8")) +
        "\n" +
        expression,
      {},
      { timeout: 1000 },
    );
  assert.throws(
    () => execute("default-later-parameter", "laterDefault()"),
    /Cannot access 'second' before initialization/,
  );
  assert.throws(
    () => execute("invalid-default-invocation", "defaultInvokedTooEarly()"),
    /Cannot access 'later' before initialization/,
  );
  assert.equal(execute("generic-default", "genericDefault(true)"), null);
  assert.equal(
    execute("generic-rigid-default", "undefinedRigidDefault(undefined)"),
    undefined,
  );
  for (const seed of [true, false]) {
    assert.equal(
      execute("generic-rigid-default", `genericDeferredDefault(${seed})`),
      seed,
    );
    // Both formerly gated safe defaults now verify.
    assert.equal(
      execute("default-deferred-capture", `deferredDefaultCapture(${seed})`),
      seed,
    );
    assert.equal(
      execute("default-deferred-capture", `deferredChain(${seed})`),
      false,
    );
    assert.equal(
      execute("generic-rigid-default", `rigidDefault(${seed})`),
      seed,
    );
    assert.equal(
      execute("generic-defaults", `genericDefaultResult(${seed})`),
      seed,
    );
    assert.equal(
      execute("generic-defaults", `genericDefaultCallback(${seed})`),
      seed,
    );
    assert.equal(
      execute("generic-defaults", `genericDefaultValue(${seed})`),
      false,
    );
    assert.equal(
      execute("default-parameter-scope", `initializedDefaults(${seed})`),
      seed,
    );
    assert.equal(
      execute("default-parameter-scope", `defaultEffects(${seed})`),
      false,
    );
    assert.equal(
      execute("default-parameter-scope", `suppliedDefaultSkipsEffect(${seed})`),
      seed,
    );
    assert.equal(
      execute("default-parameter-scope", `nonTrailingDefault(${seed})`),
      seed,
    );
  }
  console.log(
    "default initialization: ordered scope, effects, skipped defaults and forged later read checked",
  );
}

/** Both entry points must refuse executable defaults lacking a scheme certificate. */
export function checkSchemeDefaults(verifier: string, artifacts: string): void {
  // Extraction must refuse before inspecting the evidence. Production cannot
  // emit evidence for this program, but consumption still needs a JSON file.
  writeFileSync(join(artifacts, "evidence.json"), "{}");
  for (const mode of ["--produce-source-claims", "--check-source-claims"]) {
    const result = spawnSync(
      verifier,
      [
        mode,
        join(artifacts, "fragment.json"),
        join(artifacts, "claims.json"),
        join(artifacts, "source.ts"),
        join(artifacts, "evidence.json"),
        ...(mode === "--produce-source-claims" ? ["12"] : []),
      ],
      { encoding: "utf8", timeout: 30_000 },
    );
    assert.ifError(result.error);
    assert.equal(result.signal, null);
    assert.equal(result.status, 1);
    assert.match(
      result.stdout + result.stderr,
      /body requires a variable, a primitive literal, an assignment, a call or a closure/,
    );
    const diagnostic = readDiagnostic(result.stdout + result.stderr);
    assert(diagnostic?.kind === "source-refusal");
    assert.equal(diagnostic.sourceMap.role, "generic-validation");
    assert(diagnostic.sourceMap.pos[0] < diagnostic.sourceMap.pos[1]);
  }
}

/** A proposed well-typed closure still cannot read its capture during TDZ.
 * This must be a located refusal from both independent entry points. */
export function checkEarlyDefault(verifier: string, artifacts: string): void {
  writeFileSync(join(artifacts, "evidence.json"), "{}");
  for (const mode of ["--produce-source-claims", "--check-source-claims"]) {
    const result = spawnSync(
      verifier,
      [
        mode,
        join(artifacts, "fragment.json"),
        join(artifacts, "claims.json"),
        join(artifacts, "source.ts"),
        join(artifacts, "evidence.json"),
        ...(mode === "--produce-source-claims" ? ["12"] : []),
      ],
      { encoding: "utf8", timeout: 30_000 },
    );
    assert.ifError(result.error);
    assert.equal(result.signal, null);
    assert.equal(result.status, 1);
    const output = result.stdout + result.stderr;
    assert.match(output, /pending closure cannot be invoked or exposed/);
    const diagnostic = readDiagnostic(output);
    assert(diagnostic?.kind === "source-refusal");
    assert.equal(diagnostic.sourceMap.role, "binding-annotation");
    assert(diagnostic.sourceMap.pos[0] < diagnostic.sourceMap.pos[1]);
  }
}
