#!/usr/bin/env node
// Report original producer claims, without repairing them or running mutation tests.
const fs = require("node:fs");
const path = require("node:path");
const os = require("node:os");
const { spawnSync } = require("node:child_process");
const { fromSkjs, verifySkjs } = require("./tools/annotate-source.mts");
const tscClaims = require("./tools/tsc-claims.mts");
const { projectFor } = require("./tools/parse-source.mts");
const ts = require(
  require.resolve("typescript/unstable/ast", {
    paths: [path.join(__dirname, "tools")],
  }),
);
const { groups, supported } = require("./report-viewer/examples.js");
const root = path.resolve(__dirname, "..");
process.chdir(root);
let build = false,
  verbose = false,
  shard = null,
  claimsPath = null,
  // Both producers by default: the comparison is the point. Either can be
  // asked for alone, which is also how one is measured without the other.
  producers = { skjs: true, tsc: true },
  binary = process.env.SKJS_BIN;
for (let i = 2; i < process.argv.length; i++) {
  const arg = process.argv[i];
  if (arg === "--build") build = true;
  else if (arg === "--verbose") verbose = true;
  else if (arg === "--skjs" && process.argv[i + 1]) binary = process.argv[++i];
  else if (arg === "--only" && process.argv[i + 1]) {
    const named = process.argv[++i].split(",");
    for (const name of named)
      if (!(name in producers)) throw Error(`unknown producer '${name}'`);
    producers = { skjs: named.includes("skjs"), tsc: named.includes("tsc") };
  }
  // A worker checks the files of one shard and reports them as data. The parent
  // hands it the claims so the producer still runs exactly once for the run.
  else if (arg === "--shard" && process.argv[i + 1]) shard = process.argv[++i];
  else if (arg === "--claims" && process.argv[i + 1])
    claimsPath = process.argv[++i];
  else
    throw Error(
      "usage: examples.js [--build] [--verbose] [--only skjs|tsc] [--skjs BIN] [--shard i:n --claims FILE]",
    );
}
const verifier = path.join(__dirname, "lean/.lake/build/bin/verifier");
const work = fs.mkdtempSync(path.join(os.tmpdir(), "examples-"));
process.on("exit", () => fs.rmSync(work, { recursive: true, force: true }));
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
    (file === "verification/tests/partial-claims.ts" && name === "complete") ||
    // An incompleteness witness that needs no claim repair: SKJS rejects the
    // annotation and the verifier establishes it from the producer's own
    // partial export.
    file === "verification/tests/skjs-incomplete/undefined-completes.ts"
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
  if (result.location?.kind === "parameter-claim")
    return ["✗", "parameter claim differs from annotation"];
  return ["✗", "proof search failed"];
}
// Colors supplement the labels; logs and NO_COLOR output stay plain. A worker
// writes to a pipe, so its own stdout is never a terminal: whether to colour is
// the parent's decision and travels with the work rather than being asked again
// somewhere it cannot be answered.
const colorEnv = process.env.VERIFY_COLOR;
function color(code, text, stream = process.stdout) {
  const wanted = colorEnv
    ? colorEnv === "1"
    : stream.isTTY && process.env.TERM !== "dumb" && !process.env.NO_COLOR;
  return wanted ? `\x1b[${code}m${text}\x1b[0m` : text;
}
const colorForWorkers = color(0, "x") === "x" ? "0" : "1";
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
  if (!shard)
    console.log(
      "\nExample outcomes — original claims, no repairs applied. Each producer" +
        " reads accepted→derived: its own verdict on the program, then whether" +
        " the verifier derives the claims it made. ⚠ marks an SKJS acceptance" +
        " its own claims do not establish. The tsc column carries no ⚠: that" +
        " producer states no current-content assertions, so a cell read after" +
        " a write fails there by its own limits (tests/tsc-claims/README.md).",
    );
  // One producer run for every example. A container start costs more than
  // checking any of these files, so the loop used to spend most of its time
  // starting containers; the claim array names each file, so one run serves
  // them all.
  const sources = [...new Set(groups.flatMap((g) => g.files))];
  // Asking for one producer runs only that producer: the SKJS collection is
  // a container start and a check over every example, which is the run's
  // largest single cost and is pure waste when its column is not shown.
  const collected = !producers.skjs
    ? { stdout: "[]", stderr: "" }
    : claimsPath
      ? { stdout: fs.readFileSync(claimsPath, "utf8"), stderr: "" }
      : run("bash", [
          "verification/skjs.sh",
          "--emit-skjs-type-claims",
          ...sources,
        ]);
  const claims = JSON.parse(collected.stdout);
  if (!Array.isArray(claims))
    throw Error("producer did not return a claim array");
  // Diagnostics stay with the file they belong to. SKJS prefixes each with the
  // path it is about, so the combined stream partitions on those markers.
  const diagnostics = new Map();
  {
    let current = null;
    for (const line of (collected.stderr || "").split("\n")) {
      const named = /^File "(?:\/work\/skjs\/)?(.*?)",/.exec(line);
      if (named && sources.includes(named[1])) current = named[1];
      if (current)
        diagnostics.set(
          current,
          (diagnostics.get(current) || "") + line + "\n",
        );
    }
  }
  // Each file is checked on its own and reports what it found, so the work can
  // be spread across processes and still be printed in the order it was
  // written. Counting happens where the lines are merged, not where they are
  // produced, so a worker and a plain run agree.
  // One checker for the files this process examines, for the same reason there
  // is one producer run: loading it costs more than reading any one file. A
  // worker loads its own shard, not the whole corpus.
  let mine = sources;
  const examine = (file) => {
    const lines = [];
    const tally = {
      verified: 0,
      failed: 0,
      unavailable: 0,
      unexpected: 0,
      errors: 0,
      producerAccepted: 0,
      producerRejected: 0,
      producerUnknown: 0,
    };
    const say = (text) => lines.push(String(text).replace(/\n$/, ""));
    let verified = 0,
      failed = 0,
      unavailable = 0,
      unexpected = 0,
      errors = 0,
      producerAccepted = 0,
      producerRejected = 0,
      producerUnknown = 0;
    try {
      const source = fs.readFileSync(file, "utf8");
      // What TypeScript's own checker claims at the same sites, put through
      // the same verifier. A second producer disagreeing with the first is
      // the comparison this corpus exists for; a producer that cannot state
      // a site leaves its functions unmarked rather than failing the run.
      const fromTsc = new Map();
      // The functions the producer could state in full. One it could not is a
      // gap in the claims, not a verdict about them, so it reads `·`.
      let stated = new Set();
      let tscAccepted = null;
      if (producers.tsc)
        try {
          const { doc, ast, accepted } = tscClaims.produce(file);
          tscAccepted = accepted;
          stated = new Set(doc.functions.map((g) => g.name));
          // Producing evidence checks it, so one run answers the whole file.
          // Only a file that fails is split, and only to say which function
          // failed; a file that verifies needs no second look.
          const claimed = new Set(doc.functions.map((g) => g.name));
          const attempt = (document) => {
            const astFile = path.join(work, "tsc.ast.json");
            const claimsFile = path.join(work, "tsc.claims.json");
            fs.writeFileSync(astFile, JSON.stringify({ ...ast, file }));
            fs.writeFileSync(claimsFile, JSON.stringify(document));
            return (
              run(verifier, [
                "--produce-source-claims",
                astFile,
                claimsFile,
                file,
                path.join(work, "tsc.evidence.json"),
                "10",
              ]).status === 0
            );
          };
          if (attempt(doc)) for (const name of claimed) fromTsc.set(name, true);
          else
            for (const name of claimed)
              fromTsc.set(
                name,
                attempt({
                  ...doc,
                  functions: doc.functions.filter((g) => g.name === name),
                }),
              );
        } catch (error) {
          void error;
        }
      // Without its column there is nothing to attribute, so neither the
      // report nor the verification is built.
      const report = producers.skjs
        ? fromSkjs(source, file, claims, "skjs")
        : { functions: [] };
      const { results } = producers.skjs
        ? verifySkjs(file, source, claims, file, report, verifier, 10)
        : { results: [] };
      const functions = projectFor(path.resolve(file))
        .program.getSourceFile(path.resolve(file))
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
        if (producers.skjs) {
          if (producer === "complete") producerAccepted++;
          else if (producer === "aborted") producerRejected++;
          else producerUnknown++;
        }
        const [mark, label] = outcome(result);
        // Each producer answers two questions: did it accept the program,
        // and can the verifier derive the claims it made. They are different
        // questions, so each producer shows both, as `accepted→derived`.
        const tscProof = fromTsc.has(f.name.text)
          ? fromTsc.get(f.name.text)
            ? "✓"
            : "✗"
          : "·";
        const tscOwn = tscAccepted === null ? "·" : tscAccepted ? "✓" : "✗";
        const pair = (own, proof, flag) =>
          `${marked(own, own)}→${marked(proof, proof)}` +
          (flag && own === "✓" && proof === "✗" ? color(33, " ⚠") : "");
        if (producers.skjs) {
          if (accepted) verified++;
          else if (mark === "?") unavailable++;
          else failed++;
        }
        // Expected outcomes are policy about SKJS's claims; with that column
        // off there is no policy to hold anything to.
        const matches =
          !producers.skjs ||
          (index >= 0 && accepted === expectedVerified(file, f.name.text));
        if (!matches) unexpected++;
        const disagrees =
          (producer === "complete" && mark === "✗") ||
          (producer === "aborted" && accepted);
        say(
          `    ${f.name.text}: ` +
            [
              producers.skjs && `SKJS ${pair(producerMark, mark, true)}`,
              producers.tsc && `tsc ${pair(tscOwn, tscProof, false)}`,
            ]
              .filter(Boolean)
              .join(" · ") +
            `${verbose ? ` — ${label}` : ""}${matches ? "" : color(31, " ✗ unexpected outcome")}`,
        );
        if (verbose && result?.detail)
          say("      " + result.detail.replace(/\n/g, "\n      "));
      }
    } catch (error) {
      errors++;
      say(color(31, "    ✗ runner error: " + error.message));
    }

    Object.assign(tally, {
      verified,
      failed,
      unavailable,
      unexpected,
      errors,
      producerAccepted,
      producerRejected,
      producerUnknown,
    });
    return { lines, tally };
  };

  // A worker reports its shard as data and leaves the presentation alone.
  if (shard) {
    const [index, total] = shard.split(":").map(Number);
    mine = sources.filter((_, at) => at % total === index);
    for (const file of mine)
      process.stdout.write(JSON.stringify({ file, ...examine(file) }) + "\n");
    process.exit(0);
  }

  // Files are independent, so they are checked together and merged in order.
  // One worker per core, never more than there are files. Measured on a
  // twelve-core machine: 4.19s at one worker, 1.95s at eight, 1.77s at twelve,
  // and 2.09s at twenty-three, where the workers outnumber the cores and start
  // competing. The curve is flat either side of the core count, so this needs
  // no tuning knob.
  const width = Math.max(1, Math.min(os.cpus().length, sources.length));
  const findings = new Map();
  if (width > 1 && sources.length > 1) {
    const shared = path.join(os.tmpdir(), `example-claims-${process.pid}.json`);
    fs.writeFileSync(shared, collected.stdout);
    // Started together and waited for once. Spawning them one at a time would
    // run them one at a time, which is slower than not sharding at all: each
    // worker would pay its own start before the next could begin.
    const quote = (text) => JSON.stringify(String(text));
    const outputs = [];
    for (let index = 0; index < width; index++)
      outputs.push(
        path.join(os.tmpdir(), `example-shard-${process.pid}-${index}.json`),
      );
    const flags = [
      ...(verbose ? ["--verbose"] : []),
      ...(binary ? ["--skjs", binary] : []),
      ...(producers.skjs && producers.tsc
        ? []
        : ["--only", producers.skjs ? "skjs" : "tsc"]),
    ]
      .map(quote)
      .join(" ");
    try {
      run("bash", [
        "-c",
        outputs
          .map(
            (out, index) =>
              `VERIFY_COLOR=${colorForWorkers} ${quote(process.execPath)} ${quote(__filename)} --shard ${index}:${width} --claims ${quote(shared)} ${flags} > ${quote(out)} &`,
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
    } finally {
      fs.rmSync(shared, { force: true });
      for (const out of outputs) fs.rmSync(out, { force: true });
    }
  }

  for (const group of groups) {
    console.log("\n" + group.label);
    for (const file of group.files) {
      console.log("  " + file);
      files++;
      const found = findings.get(file) || { file, ...examine(file) };
      for (const line of found.lines) console.log(line);
      // Producer diagnostics belong to the run that collected them, not to a
      // worker that was handed the claims afterwards.
      if (verbose && diagnostics.has(file))
        process.stdout.write(diagnostics.get(file));
      verified += found.tally.verified;
      failed += found.tally.failed;
      unavailable += found.tally.unavailable;
      unexpected += found.tally.unexpected;
      errors += found.tally.errors;
      producerAccepted += found.tally.producerAccepted;
      producerRejected += found.tally.producerRejected;
      producerUnknown += found.tally.producerUnknown;
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
