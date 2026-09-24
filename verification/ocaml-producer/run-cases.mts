// Fast iteration: check only the inventory cases whose file names match, each
// against its expected outcome, phase and diagnostic.
//   node verification/ocaml-producer/run-cases.mts module- generic-rest
// With no pattern, every case. This is the loop `test.mts` runs first; the
// rest of `test.mts` (pinned imports, tampering controls, the reader) is not
// run here.
import assert from "node:assert/strict";
import { join, resolve } from "node:path";
import { check, type Outcome } from "./check.mts";
import { cases, type Case } from "./cases.mts";
import { tsconfigOf } from "../tools/declaration-graph.mts";

const here = import.meta.dirname;

/** Run one case and require its expected outcome. */
export function expectCase(test: Case): Outcome {
  const result = check(join(here, "examples", `${test.file}.ts`),
    test.project ? tsconfigOf(resolve(here, "../..", test.project)) : undefined);
  assert.equal(result.status, test.status, `${test.file}: ${JSON.stringify(result)}`);
  assert.equal(result.phase, test.phase, `${test.file}: wrong boundary`);
  if (test.diagnostic) {
    assert.notEqual(result.status, "verified");
    if (result.status !== "verified")
      assert.match(result.detail, test.diagnostic, `${test.file}: wrong failure`);
  }
  return result;
}

if (import.meta.filename === resolve(process.argv[1] ?? "")) {
  const patterns = process.argv.slice(2);
  const selected = cases.filter((c) => !patterns.length || patterns.some((p) => c.file.includes(p)));
  if (!selected.length) {
    process.stderr.write(`no case matches ${patterns.join(" ")}\n`);
    process.exit(2);
  }
  let failed = 0;
  for (const test of selected) {
    try {
      const result = expectCase(test);
      process.stdout.write(`${test.file}: ${result.status} (${result.phase}, ${test.kind})\n`);
    } catch (error) {
      failed++;
      process.stdout.write(`${test.file}: FAILED ${error instanceof Error ? error.message.split("\n")[0] : error}\n`);
    }
  }
  process.stdout.write(`${selected.length - failed} of ${selected.length} cases as expected\n`);
  process.exitCode = failed ? 1 : 0;
}
