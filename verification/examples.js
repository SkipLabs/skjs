#!/usr/bin/env node
// Report original producer claims, without repairing them or running mutation tests.
const fs = require("node:fs");
const path = require("node:path");
const { spawnSync } = require("node:child_process");
const ts = require("./tools/node_modules/typescript");
const { fromSkjs, verifySkjs } = require("./tools/annotate-source.js");
const { groups, supported } = require("./report-viewer/examples.js");
const root = path.resolve(__dirname, "..");
process.chdir(root);
let build = false,
  verbose = false,
  binary = process.env.SKJS_BIN;
for (let i = 2; i < process.argv.length; i++) {
  const arg = process.argv[i];
  if (arg === "--build") build = true;
  else if (arg === "--verbose") verbose = true;
  else if (arg === "--skjs" && process.argv[i + 1]) binary = process.argv[++i];
  else throw Error("usage: examples.js [--build] [--verbose] [--skjs BIN]");
}
const verifier = path.join(__dirname, "lean/.lake/build/bin/verifier");
function run(command, args) {
  const r = spawnSync(command, args, {
    cwd: root,
    encoding: "utf8",
    timeout: 120000,
    maxBuffer: 32 * 1024 * 1024,
    env: { ...process.env, ...(binary ? { SKJS_BIN: binary } : {}) },
  });
  if (r.error || r.signal) throw Error(String(r.error || r.signal));
  return r;
}
// Expected outcomes are corpus policy, not evidence. The partial fixture contains
// two invalid definitions and a valid one; a rejection alone proves no bug.
function expectedVerified(file, name) {
  return (
    supported.includes(file) ||
    (file === "verification/tests/partial-claims.ts" && name === "complete")
  );
}
// Match the visualizer: failure to find a proof is distinct from inability to
// attempt it, and neither establishes that the claim is false.
const incompleteInput = new Set([
  "missing-expression-claim",
  "missing-environment-claim",
  "source-limitation",
]);
function outcome(result) {
  if (!result) return ["?", "no producer claim"];
  if (result.status === "verified") return ["✓", "verified"];
  if (result.location?.reason === "non-invariant-cell-contract")
    return ["?", "non-invariant cell contract"];
  if (
    result.status === "unsupported" ||
    result.location?.kind === "source-limitation"
  )
    return ["?", "unsupported source"];
  if (result.location?.kind === "unavailable-type-claim")
    return ["?", "required type unavailable"];
  if (incompleteInput.has(result.location?.kind))
    return ["?", "required claim missing"];
  return ["✗", "proof search failed"];
}
// Colors supplement the labels; logs and NO_COLOR output stay plain.
function color(code, text, stream = process.stdout) {
  return stream.isTTY && process.env.TERM !== "dumb" && !process.env.NO_COLOR
    ? `\x1b[${code}m${text}\x1b[0m`
    : text;
}
function marked(mark, text) {
  return color(mark === "✓" ? 32 : mark === "✗" ? 31 : 33, text);
}
const started = Date.now();
let verified = 0,
  failed = 0,
  unavailable = 0,
  unexpected = 0,
  errors = 0,
  files = 0;
let producerAccepted = 0,
  producerRejected = 0,
  producerUnknown = 0;
try {
  if (build) {
    console.log("Building verifier for examples...");
    const r = run("lake", ["-d", "verification/lean", "build"]);
    if (r.status !== 0) throw Error(r.stderr + r.stdout);
    if (verbose) process.stdout.write(r.stdout);
    console.log(marked("✓", "✓ Lean build passed"));
  }
  console.log("\nExample outcomes — original SKJS claims; no repairs applied");
  for (const group of groups) {
    console.log("\n" + group.label);
    for (const file of group.files) {
      console.log("  " + file);
      files++;
      try {
        const collected = run("bash", [
          "verification/skjs.sh",
          "--emit-skjs-type-claims",
          file,
        ]);
        const claims = JSON.parse(collected.stdout);
        if (!Array.isArray(claims))
          throw Error("producer did not return a claim array");
        const source = fs.readFileSync(file, "utf8");
        const report = fromSkjs(source, file, claims, "skjs");
        const { results } = verifySkjs(
          file,
          source,
          claims,
          file,
          report,
          verifier,
          10,
        );
        const functions = ts
          .createSourceFile(file, source, ts.ScriptTarget.Latest, true)
          .statements.filter(
            (n) => ts.isFunctionDeclaration(n) && n.name && n.body,
          );
        if (!functions.length)
          throw Error("example contains no function definitions");
        for (const f of functions) {
          const index = report.functions.findIndex(
            (g) => g.name === f.name.text && g.namePos[0] === f.name.getStart(),
          );
          const result = index < 0 ? undefined : results[index];
          const accepted = result?.status === "verified";
          const producer = report.functions[index]?.collection?.completion;
          const producerMark =
            producer === "complete" ? "✓" : producer === "aborted" ? "✗" : "·";
          if (producer === "complete") producerAccepted++;
          else if (producer === "aborted") producerRejected++;
          else producerUnknown++;
          const [mark, label] = outcome(result);
          if (accepted) verified++;
          else if (mark === "?") unavailable++;
          else failed++;
          const matches =
            index >= 0 && accepted === expectedVerified(file, f.name.text);
          if (!matches) unexpected++;
          const disagrees =
            (producer === "complete" && mark === "✗") ||
            (producer === "aborted" && accepted);
          console.log(
            `    ${f.name.text}: SKJS ${marked(producerMark, producerMark)} · proof ${marked(mark, `${mark} — ${label}`)}${disagrees ? color(33, " ⚠ outcomes differ") : ""}${matches ? "" : color(31, " ✗ unexpected outcome")}`,
          );
          if (verbose && result?.detail)
            console.log("      " + result.detail.replace(/\n/g, "\n      "));
        }
        if (verbose && collected.stderr) process.stdout.write(collected.stderr);
      } catch (error) {
        errors++;
        console.log(color(31, "    ✗ runner error: " + error.message));
      }
    }
  }
} catch (error) {
  errors++;
  console.error(
    color(31, "✗ Example runner: " + error.message, process.stderr),
  );
}
console.log(`\nExample results (${files} files):`);
console.log(
  `  SKJS: ${color(32, `${producerAccepted} accepted`)}, ${color(producerRejected ? 31 : 32, `${producerRejected} rejected`)}, ${color(producerUnknown ? 33 : 32, `${producerUnknown} unrecorded`)}`,
);
console.log(
  `  Proof: ${color(32, `${verified} verified`)}, ${color(failed ? 31 : 32, `${failed} search failed`)}, ${color(unavailable ? 33 : 32, `${unavailable} could not check`)}`,
);
console.log(
  color(
    unexpected || errors ? 31 : 32,
    `${unexpected || errors ? "✗" : "✓"} Expected outcomes: ${unexpected} mismatches, ${errors} runner errors`,
  ),
);
console.log(
  "  Proof ✗ means no proof found, not a disproof. Repair demonstrations live in verify-test.",
);
console.log(`  Elapsed: ${Math.round((Date.now() - started) / 1000)}s`);
process.exitCode = unexpected || errors ? 1 : 0;
