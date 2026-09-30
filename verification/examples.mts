#!/usr/bin/env node
// Report what TypeScript's own checker claims over the corpus, and whether the
// verifier derives those claims.
import fs from "node:fs";
import path from "node:path";
import os from "node:os";
import { spawnSync } from "node:child_process";
// tools/tsc-claims.mts is the producer the corpus runs, through the one entry: TypeScript's own checker, stating its claims.
import { check, searchDepth, verifier } from "./ocaml-producer/check.mts";
import { functionResults } from "./tools/annotate-source.mts";
import type { SourceClaims } from "./tools/source-claims.mts";
import { messageOf } from "./tools/thrown.mts";
import { definedFunctions } from "./tools/fragment-parse.mts";
// report-viewer/examples.mts is the corpus index, which the reader lists too: which files each group holds.
import { groups } from "./report-viewer/examples.mts";

const __filename = import.meta.filename;
const __dirname = path.dirname(__filename);
const root = path.resolve(__dirname, "..");
process.chdir(root);
let build = false,
  verbose = false,
  shard: string | null = null;
for (let i = 2; i < process.argv.length; i++) {
  const arg = process.argv[i];
  if (arg === "--build") build = true;
  else if (arg === "--verbose") verbose = true;
  // A worker checks the files of one shard and reports them as data.
  else if (arg === "--shard" && process.argv[i + 1]) shard = process.argv[++i];
  else throw Error("usage: examples.mts [--build] [--verbose] [--shard i:n]");
}
const work = fs.mkdtempSync(path.join(os.tmpdir(), "examples-"));
process.on("exit", () => fs.rmSync(work, { recursive: true, force: true }));
function run(command: string, args: string[]) {
  const r = spawnSync(command, args, {
    cwd: root,
    encoding: "utf8",
    timeout: 120000,
    maxBuffer: 32 * 1024 * 1024,
  });
  if (r.error || r.signal) throw Error(String(r.error || r.signal));
  return r;
}
// Colors supplement the marks; logs and NO_COLOR output stay plain. A worker
// writes to a pipe, so its own stdout is never a terminal: whether to colour is
// the parent's decision and travels with the work rather than being asked again
// somewhere it cannot be answered.
const colorEnv = process.env.VERIFY_COLOR;
function color(
  code: number,
  text: string,
  stream: NodeJS.WriteStream = process.stdout,
) {
  const wanted = colorEnv
    ? colorEnv === "1"
    : stream.isTTY && process.env.TERM !== "dumb" && !process.env.NO_COLOR;
  return wanted ? `\x1b[${code}m${text}\x1b[0m` : text;
}
const colorForWorkers = color(0, "x") === "x" ? "0" : "1";
function marked(mark: string) {
  return color(mark === "✓" ? 32 : mark === "✗" ? 31 : 33, mark);
}
interface Tally {
  accepted: number;
  rejected: number;
  unrecorded: number;
  derived: number;
  notDerived: number;
  unstated: number;
  errors: number;
}
const empty = (): Tally => ({
  accepted: 0,
  rejected: 0,
  unrecorded: 0,
  derived: 0,
  notDerived: 0,
  unstated: 0,
  errors: 0,
});
const tallyKeys: (keyof Tally)[] = ["accepted", "rejected", "unrecorded", "derived", "notDerived", "unstated", "errors"];
const started = Date.now();
const total = empty();
let files = 0;

// Each file is checked on its own and reports what it found, so the work can
// be spread across processes and still be printed in the order it was
// written. Counting happens where the lines are merged, not where they are
// produced, so a worker and a plain run agree.
function examine(file: string) {
  const lines: string[] = [];
  const tally = empty();
  const say = (text: string) => lines.push(text.replace(/\n$/, ""));
  try {
    // What TypeScript's own checker claims, put through the verifier. A
    // function it could not state in full is a gap in the claims, not a
    // verdict about them, so it reads `·`.
    const fromTsc = new Map<string, boolean>();
    let accepted: Map<string, boolean> | null = null;
    // One pipeline run answers the whole file: the entry's search and check.
    // Only a file that fails is split, and only to say which function failed,
    // by the report writer's per-function checks over that run's Fragment and
    // claims; a file that verifies needs no second look.
    const outcome = check(file, undefined, false, "tsc");
    try {
      const at = (name: string) => path.join(outcome.artifacts, name);
      const read = (name: string) => fs.readFileSync(at(name), "utf8");
      if (fs.existsSync(at("tsc-verdicts.json")))
        accepted = new Map(Object.entries(JSON.parse(read("tsc-verdicts.json"))));
      if (outcome.status === "verified" || outcome.status === "unverified") {
        // The run named its snapshot; these name the file it is a snapshot of.
        const claims: SourceClaims = { ...JSON.parse(read("claims.json")), file };
        const results = outcome.status === "verified" ? null
          : functionResults(file, { ...JSON.parse(read("fragment.json")), file }, claims, verifier, searchDepth);
        claims.functions.forEach((g, i) => {
          const result = results?.[i];
          if (result instanceof Error && verbose) say(`    ${g.name}: ${result.message}`);
          fromTsc.set(g.name, !results || (!(result instanceof Error) && result?.status === "verified"));
        });
      } else if (verbose) say("    tsc could not state this file: " + outcome.detail);
    } finally {
      fs.rmSync(outcome.artifacts, { recursive: true, force: true });
    }
    const functions = definedFunctions(file);
    if (!functions.length) throw Error("example contains no function definitions");
    for (const f of functions) {
      const own = accepted?.has(f.name) ? (accepted.get(f.name) ? "✓" : "✗") : "·";
      const proof = fromTsc.has(f.name) ? (fromTsc.get(f.name) ? "✓" : "✗") : "·";
      if (own === "✓") tally.accepted++;
      else if (own === "✗") tally.rejected++;
      else tally.unrecorded++;
      if (proof === "✓") tally.derived++;
      else if (proof === "✗") tally.notDerived++;
      else tally.unstated++;
      say(`    ${f.name}: tsc ${marked(own)}→${marked(proof)}`);
    }
  } catch (error) {
    tally.errors++;
    say(color(31, "    ✗ runner error: " + messageOf(error)));
  }
  return { lines, tally };
}

try {
  if (build) {
    console.log("Building verifier for examples...");
    const r = run("lake", ["-d", "verification/lean", "build"]);
    if (r.status !== 0) throw Error(r.stderr + r.stdout);
    if (verbose) process.stdout.write(r.stdout);
    console.log(color(32, "✓ Lean build passed"));
  }
  const sources = [...new Set(groups.flatMap((g) => g.files))];

  // A worker reports its shard as data and leaves the presentation alone.
  if (shard) {
    const [index, count] = shard.split(":").map(Number);
    for (const file of sources.filter((_, at) => at % count === index))
      process.stdout.write(JSON.stringify({ file, ...examine(file) }) + "\n");
    process.exit(0);
  }

  console.log(
    "\nExample outcomes — TypeScript's claims. Each line" +
      " reads accepted→derived: tsc's own verdict on the function, then whether" +
      " the verifier derives the claims it made (tests/tsc-claims/README.md).",
  );
  // Files are independent, so they are checked together and merged in order.
  // One worker per core, never more than there are files: the curve is flat
  // either side of the core count, so this needs no tuning knob.
  const width = Math.max(1, Math.min(os.cpus().length, sources.length));
  const findings = new Map<string, ReturnType<typeof examine>>();
  if (width > 1) {
    const quote = (text: unknown) => JSON.stringify(String(text));
    const outputs: string[] = [];
    for (let index = 0; index < width; index++)
      outputs.push(path.join(work, `example-shard-${index}.json`));
    const flags = verbose ? " --verbose" : "";
    // Started together and waited for once: spawning them one at a time would
    // run them one at a time.
    run("bash", [
      "-c",
      outputs
        .map(
          (out, index) =>
            `VERIFY_COLOR=${colorForWorkers} ${quote(process.execPath)} ${quote(__filename)} --shard ${index}:${width}${flags} > ${quote(out)} &`,
        )
        .join("\n") + "\nwait",
    ]);
    for (const out of outputs)
      for (const line of fs
        .readFileSync(out, "utf8")
        .split("\n")
        .filter((l) => l.startsWith("{"))) {
        const found = JSON.parse(line);
        findings.set(found.file, found);
      }
  }
  for (const group of groups) {
    console.log("\n" + group.label);
    for (const file of group.files) {
      console.log("  " + file);
      files++;
      const found = findings.get(file) ?? examine(file);
      for (const line of found.lines) console.log(line);
      for (const key of tallyKeys) total[key] += found.tally[key];
    }
  }
} catch (error) {
  total.errors++;
  console.error(color(31, "✗ Example runner: " + messageOf(error), process.stderr));
}
console.log(`\nExample results (${files} files):`);
console.log(
  `  tsc: ${total.accepted} accepted, ${total.rejected} rejected, ${total.unrecorded} unrecorded`,
);
console.log(
  `  Proof: ${color(32, `${total.derived} verified`)}, ${total.notDerived} search failed, ${total.unstated} not stated`,
);
console.log(
  color(
    total.errors ? 31 : 32,
    `${total.errors ? "✗" : "✓"} Runner errors: ${total.errors}`,
  ),
);
console.log("  Proof ✗ means no proof found, not a disproof.");
console.log(`  Elapsed: ${Math.round((Date.now() - started) / 1000)}s`);
process.exitCode = total.errors ? 1 : 0;
