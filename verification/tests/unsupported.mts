#!/usr/bin/env node
import assert from "node:assert/strict";
import type { Ast, FunctionAst } from "../tools/fragment.mts";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { spawnSync } from "node:child_process";
// Boundary examples must fail for a known unsupported feature, never pass as verified.





const verifier = process.argv[2];
const dir = "verification/tests/unsupported";
const cases = {
  "calls_and_consts.ts":
    "source type outside the null/undefined/boolean/singleton fragment",
  "typeof_narrow.ts": "expression outside the stateful fragment",
  "beyond_precision.ts": "source type outside the null/undefined/boolean/singleton fragment",
  "mutable_binding.ts": "a `let` needs an initializer",
};
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "source-boundaries-"));
/** The functions of a parse the gate accepted, which is what this reads of it. */
const parsedFunctions = (stdout: string): FunctionAst[] => {
  const parsed: Ast = JSON.parse(stdout);
  return parsed.functions;
};
const run = (cmd: string, args: string[]) => {
  const r = spawnSync(cmd, args, { encoding: "utf8", timeout: 30000 });
  assert(!r.error && !r.signal, String(r.error || r.signal));
  return r;
};
try {
  assert.deepEqual(
    fs
      .readdirSync(dir)
      .filter((f) => f.endsWith(".ts"))
      .sort(),
    // This file needs real claims to reach its edge-obligation boundary;
    // null-tests.js checks it in the full suite below.
    Object.keys(cases).sort(),
  );
  for (const [name, reason] of Object.entries(cases)) {
    const file = dir + "/" + name;
    let result = run(process.execPath, [
      "verification/tools/fragment-parse.mts",
      file,
    ]);
    if (result.status === 0) {
      fs.writeFileSync(tmp + "/ast.json", result.stdout);
      // Supply signatures so newly supported syntax can reach the type gate.
      // No invented statement/expression claims should be needed for these cases.
      fs.writeFileSync(
        tmp + "/claims.json",
        JSON.stringify([
          {
            file,
            functions: parsedFunctions(result.stdout).map((f) => ({
              name: f.name,
              namePos: f.namePos,
              params: f.params,
              retType: f.retType,
              envs: [],
              exprs: [],
            })),
          },
        ]),
      );
      result = run(verifier, [
        "--produce-stateful-source",
        tmp + "/ast.json",
        tmp + "/claims.json",
        file,
        tmp + "/evidence.json",
        "8",
      ]);
    }
    assert.notEqual(
      result.status,
      0,
      name + " unexpectedly became supported; promote it to the current suite",
    );
    assert(
      (result.stderr + result.stdout).includes(reason),
      name + ": " + result.stderr + result.stdout,
    );
    console.log("  unsupported " + name + ": expected boundary");
  }
} finally {
  fs.rmSync(tmp, { recursive: true, force: true });
}
