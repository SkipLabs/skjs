#!/usr/bin/env node
/*
 * Corpus census: run the source pipeline over every function in a corpus and
 * report one outcome per function.
 *
 * This answers "how much verifies", which the suite in run.sh does not: those
 * tests each argue that one boundary holds, and report a boolean. Here nothing
 * is asserted. A refusal is an outcome with a reason, not a failure, so the
 * reasons can be counted and the largest group chosen as the next thing to
 * widen. Progress is the diff against a recorded baseline.
 *
 * Functions are censused one per file. The corpus sources are SKJS regression
 * tests that also hold classes and ambient declarations, and the source gate
 * rejects a whole file on the first of those, so a per-file request would
 * report nothing at all. Dependencies are not carried along: a function using
 * an ambient declaration from its original file is reported as unresolved
 * rather than repaired.
 *
 * Phases are split because SKJS runs in a container: `--extract` writes the
 * per-function files, the caller exports claims for all of them in one
 * invocation, and `--report` consumes those claims. See verification/census.sh.
 */
import fs from "node:fs";
import path from "node:path";
import { spawnSync } from "node:child_process";
import { close, parseFile } from "./fragment-parse.mts";
import { listFunctions, listFunctionsOf } from "./extract-functions.mts";

/* A corpus states how to find its sources, not which they are. The resolved
 * list is a derived fact and lives in the baseline, where every row names its
 * source file: a corpus that grows or shrinks shows up there as added and
 * removed rows, reviewed like any other movement, and never as a second list
 * of filenames to keep in step with the first. */
type Corpus = {
  name: string;
  description?: string;
  select: { since: string; paths: string[] };
};
type Entry = { slug: string; source: string; fn: string };

/* Outcomes are `stage:reason`, most advanced stage last. A reason is the
 * producer's own text, normalized: positions and identifiers are dropped so
 * that the same refusal groups across functions. The normalization is
 * heuristic because refusals are English sentences; a stable code from each
 * producer would replace it. */
const GATE = "gate", CLAIMS = "claims", UNPROVED = "unproved", OK = "verified";
/* A function the producer itself rejected states nothing to check, so it is
 * not a boundary of the verified fragment and does not belong in the same
 * count. Corpus sources are error tests: most functions in them are wrong on
 * purpose, and counting those as unverified reports the corpus's design as
 * this pipeline's shortfall. */
const REJECTED = "skjs-rejected";

/** Which functions the producer reported an error in, by slug, read from its
 * own diagnostics. A warning is not a rejection: the claims are still good. */
function producerRejected(errPath: string | undefined): Set<string> {
  const out = new Set<string>();
  if (!errPath || !fs.existsSync(errPath)) return out;
  for (const block of fs.readFileSync(errPath, "utf8").split(/(?=^File ")/m)) {
    const named = /^File "([^"]+)"/.exec(block);
    if (named && /^error:/m.test(block))
      out.add(path.basename(named[1]).replace(/\.ts$/, ""));
  }
  return out;
}

function reason(text: string): string {
  const first = (text.split("\n").find(l => l.trim()) ?? "unknown").trim();
  return first
    .replace(/^(gate|error):\s*/, "")
    .replace(/\(line \d+,? col(umn)? \d+\)/g, "")
    // Single quotes carry the source's own identifiers, which differ per
    // function; backticks carry the construct, which is the whole point.
    .replace(/'[^']*'/g, "'_'")
    .replace(/\s+/g, " ")
    .trim()
    .slice(0, 90);
}

/* `since` is the first commit of the arc, so the range starts at its parent.
 * A path the arc deleted is absent from both ends and never listed; one it
 * deleted after this range would be, so existence is checked too. */
function resolve(corpus: Corpus): string[] {
  const { since, paths } = corpus.select;
  const r = spawnSync("git",
    ["diff", "--name-only", `${since}~1..HEAD`, "--", ...paths],
    { encoding: "utf8" });
  if (r.status !== 0) throw Error(`census: cannot resolve corpus: ${r.stderr}`);
  const sources = r.stdout.split("\n").filter(l => l && fs.existsSync(l)).sort();
  if (!sources.length) throw Error(`census: corpus '${corpus.name}' selected nothing`);
  return sources;
}

/* A file the range only appended a case to still holds everything it held
 * before, and those functions are not what the corpus is about: they were not
 * introduced by this work, so their coverage says nothing about it. Only the
 * functions the range added are censused; a file that did not exist then
 * contributes all of its own. */
function introduced(source: string, since: string): { name: string; text: string }[] {
  const now = listFunctions(source);
  const before = spawnSync("git", ["show", `${since}~1:${source}`], { encoding: "utf8" });
  if (before.status !== 0) return now;
  const had = new Set(listFunctionsOf(`${source}.before.ts`, before.stdout));
  return now.filter(f => !had.has(f.name));
}

function extract(corpus: Corpus, dir: string): void {
  fs.writeFileSync(`${dir}/tsconfig.json`, JSON.stringify({
    extends: "../tsconfig.json", include: ["*.ts"],
  }));
  const index: Entry[] = [];
  const taken = new Set<string>();
  const { since } = corpus.select;
  for (const source of resolve(corpus)) {
    for (const { name, text } of introduced(source, since)) {
      const slug = `${path.basename(source, ".ts")}__${name}`;
      if (taken.has(slug)) throw Error(`duplicate census slug ${slug}`);
      taken.add(slug);
      fs.writeFileSync(`${dir}/${slug}.ts`, text + "\n");
      index.push({ slug, source, fn: name });
    }
  }
  fs.writeFileSync(`${dir}/index.json`, JSON.stringify(index, null, 2));
  close();
  console.error(`census: extracted ${index.length} functions from ${new Set(index.map(e => e.source)).size} sources since ${corpus.select.since}`);
}

function report(dir: string, claimsPath: string, verifier: string,
                errPath?: string): Entry_Result[] {
  const index: Entry[] = JSON.parse(fs.readFileSync(`${dir}/index.json`, "utf8"));
  const raw: any[] = JSON.parse(fs.readFileSync(claimsPath, "utf8"));
  const byFile = new Map(raw.map(f => [f.file, f]));
  const rejected = producerRejected(errPath);
  const results: Entry_Result[] = [];
  for (const e of index) {
    const file = `${dir}/${e.slug}.ts`;
    results.push({ ...e, outcome: rejected.has(e.slug) ? REJECTED
      : outcomeFor(file, e, byFile, verifier, dir) });
  }
  return results;
}

type Entry_Result = Entry & { outcome: string };

function outcomeFor(file: string, e: Entry, byFile: Map<string, any>,
                    verifier: string, dir: string): string {
  let ast;
  try {
    ast = parseFile(file);
  } catch (err: any) {
    return `${GATE}:${reason(String(err?.message ?? err))}`;
  }
  const exported = byFile.get(file);
  if (!exported) return `${CLAIMS}:no export for this file`;
  const fn = (exported.functions ?? []).find((f: any) => f.name === e.fn);
  if (!fn) return `${CLAIMS}:function absent from the export`;
  // Sites SKJS declined to state are not screened here. Some unavailable
  // sites are benign — every function carries an unavailable `this` entry —
  // and only the verifier knows which ones its extraction actually needs.

  const ap = `${dir}/.attempt.ast`, cp = `${dir}/.attempt.claims`;
  const ep = `${dir}/.attempt.evidence`;
  fs.writeFileSync(ap, JSON.stringify(ast));
  fs.writeFileSync(cp, JSON.stringify([exported]));
  const produced = spawnSync(verifier,
    ["--produce-stateful-source", ap, cp, file, ep, "10"], { encoding: "utf8" });
  if (produced.error || produced.signal)
    return `${UNPROVED}:${reason(String(produced.error ?? produced.signal))}`;
  if (produced.status !== 0) return `${UNPROVED}:${reason(produced.stderr)}`;
  // A produced certificate that the independent consumer rejects is a defect,
  // not a census row: report it loudly rather than counting it as verified.
  const checked = spawnSync(verifier,
    ["--check-stateful-source", ap, cp, file, ep], { encoding: "utf8" });
  if (checked.status !== 0) return `INCONSISTENT:${reason(checked.stderr)}`;
  return OK;
}

function render(name: string, results: Entry_Result[]): string {
  const rows = results.map(r => `${r.outcome}\t${r.source}\t${r.fn}`).sort();
  const counts = new Map<string, number>();
  for (const r of results) {
    // Both outcomes without a reason are whole stages; everything else is
    // `stage:reason` and the stage is what precedes the colon.
    const stage = r.outcome === OK || r.outcome === REJECTED
      ? r.outcome : r.outcome.slice(0, r.outcome.indexOf(":"));
    counts.set(stage, (counts.get(stage) ?? 0) + 1);
  }
  const verified = counts.get(OK) ?? 0;
  const reachable = results.length - (counts.get(REJECTED) ?? 0);
  const head = [
    `# census: ${name}`,
    `# ${verified}/${reachable} verified, of ${results.length} functions`,
    ...[...counts].sort((a, b) => b[1] - a[1]).map(([k, v]) => `#   ${k}: ${v}`),
    "#",
  ];
  return head.concat(rows).join("\n") + "\n";
}

/** The reasons, largest group first: the next boundary worth widening. */
function histogram(results: Entry_Result[]): string {
  const counts = new Map<string, number>();
  for (const r of results) {
    if (r.outcome === OK || r.outcome === REJECTED) continue;
    counts.set(r.outcome, (counts.get(r.outcome) ?? 0) + 1);
  }
  return [...counts].sort((a, b) => b[1] - a[1]).slice(0, 15)
    .map(([k, v]) => `  ${String(v).padStart(4)}  ${k}`).join("\n");
}

const [mode, corpusPath, dir, claimsPath, verifier, ...rest] = process.argv.slice(2);
const corpus: Corpus = JSON.parse(fs.readFileSync(corpusPath, "utf8"));
if (mode === "--extract") {
  extract(corpus, dir);
} else if (mode === "--report") {
  const errFlag = rest.indexOf("--producer-errors");
  const results = report(dir, claimsPath, verifier,
    errFlag < 0 ? undefined : rest[errFlag + 1]);
  const rendered = render(corpus.name, results);
  const baselineFlag = rest.indexOf("--baseline");
  const baseline = baselineFlag < 0 ? null : rest[baselineFlag + 1];
  const verified = results.filter(r => r.outcome === OK).length;
  const rejected = results.filter(r => r.outcome === REJECTED).length;
  process.stdout.write(`${verified}/${results.length - rejected} verified` +
    ` (${rejected} of ${results.length} rejected by the producer, nothing to check)` +
    `\n\nTop refusals:\n${histogram(results)}\n`);
  const broken = results.filter(r => r.outcome.startsWith("INCONSISTENT"));
  if (!baseline) {
    process.stdout.write(`\n${rendered}`);
  } else if (rest.includes("--update") || !fs.existsSync(baseline)) {
    fs.writeFileSync(baseline, rendered);
    process.stdout.write(`\nbaseline written: ${baseline}\n`);
  } else {
    const was = fs.readFileSync(baseline, "utf8");
    if (was === rendered) process.stdout.write(`\nbaseline unchanged: ${baseline}\n`);
    else {
      process.stdout.write(`\nbaseline differs: ${baseline} (rerun with --update to accept)\n`);
      process.stdout.write(diff(was, rendered));
    }
  }
  if (broken.length) {
    process.stderr.write(`\n${broken.length} certificate(s) produced but rejected by the consumer:\n`);
    for (const b of broken) process.stderr.write(`  ${b.source} ${b.fn}: ${b.outcome}\n`);
    process.exit(1);
  }
  close();
} else {
  process.stderr.write("usage: census.mts --extract|--report <corpus.json> <dir> [<claims> <verifier> [--baseline <path> [--update]]]\n");
  process.exit(2);
}

/** Line-wise, so a moved outcome reads as one loss and one gain. */
function diff(was: string, now: string): string {
  const before = new Set(was.split("\n").filter(l => l && !l.startsWith("#")));
  const after = new Set(now.split("\n").filter(l => l && !l.startsWith("#")));
  const out: string[] = [];
  for (const line of after) if (!before.has(line)) out.push(`  + ${line}`);
  for (const line of before) if (!after.has(line)) out.push(`  - ${line}`);
  return out.length ? out.sort((a, b) => a.slice(4).localeCompare(b.slice(4))).join("\n") + "\n" : "";
}
