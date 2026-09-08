#!/usr/bin/env node
// Boundary examples must fail for a known unsupported feature, never pass as verified.
const assert = require("node:assert/strict");
const fs = require("node:fs");
const os = require("node:os");
const path = require("node:path");
const { spawnSync } = require("node:child_process");
const verifier = process.argv[2];
const dir = "verification/tests/unsupported";
const cases = {
  "calls_and_consts.ts": "expression outside the stateful source slice",
  "typeof_narrow.ts": "expression outside the stateful source slice",
  "beyond_precision.ts": "expression outside the stateful source slice",
  "mutable_binding.ts": "only `const` bindings",
};
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "source-boundaries-"));
const run = (cmd, args) => {
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
    Object.keys(cases).sort(),
  );
  for (const [name, reason] of Object.entries(cases)) {
    const file = dir + "/" + name;
    let result = run(process.execPath, [
      "verification/tools/parse-source.js",
      file,
    ]);
    if (result.status === 0) {
      fs.writeFileSync(tmp + "/ast.json", result.stdout);
      // Decoding the unsupported source must fail before any candidate is needed.
      fs.writeFileSync(
        tmp + "/claims.json",
        JSON.stringify([{ file, functions: [] }]),
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
