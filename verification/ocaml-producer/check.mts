import { execFile, spawnSync } from "node:child_process";
import { mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { basename, resolve, join } from "node:path";
import { createHash } from "node:crypto";
import { parseFile } from "../tools/fragment-parse.mts";
import { clientErrors, tsconfigOf, type SeenDiagnostic } from "../tools/declaration-graph.mts";
import { readDiagnostic } from "../tools/diagnostic.mts";
import { presentObligation } from "../tools/diagnostic-view.mts";

const here = import.meta.dirname;
const repo = resolve(here, "../..");
export const verifier =
  process.env.VERIFIER ??
  resolve(repo, "verification/lean/.lake/build/bin/verifier");
export type Phase = "source" | "proposal" | "search" | "check";
export type Outcome =
  | {
      status: "verified";
      artifacts: string;
      functions: string[];
      /** The source spans of the module initialization's top-level
       * statements, which Lean checked as one unit; empty when the module
       * has no initialization code. */
      initialization: [number, number][];
      phase: "check";
    }
  | {
      status: "unsupported" | "unverified" | "error";
      artifacts: string;
      detail: string;
      phase: Phase;
    };
/** The fuel proof search is given. */
export const searchDepth = 12;
/** Wall-clock limit on each external step (the parser, the producer, the
 * search, the check). A step that exceeds it is killed and the case is an
 * error naming the step and the limit, never a verdict. */
export const stepTimeoutMs = 30_000;
function run(command: string, args: string[]) {
  const p = spawnSync(command, args, {
    cwd: repo,
    encoding: "utf8",
    timeout: stepTimeoutMs,
    maxBuffer: 16 * 1024 * 1024,
  });
  const step = [
    basename(command),
    ...args.filter((a) => a.startsWith("--")),
  ].join(" ");
  if ((p.error as NodeJS.ErrnoException | undefined)?.code === "ETIMEDOUT")
    throw Error(
      `timeout: ${step} did not finish within ${stepTimeoutMs / 1000} s`,
    );
  if (p.error || p.signal || p.status === null)
    throw Error(
      `${step}: ${p.error?.message ?? p.signal ?? "no exit status"}`,
    );
  return {
    code: p.status,
    out: p.stdout,
    detail: p.stderr.trim() || p.stdout.trim(),
  };
}
/** A failed search names the obligation it could not establish and why, in
 * source terms: the reader's summary of the verifier's structured record, as
 * the line `obligation: …` after the verifier's own first line. Display only;
 * a record the reader refuses adds nothing. */
function namingTheObligation(detail: string, source: string): string {
  const record = readDiagnostic(detail);
  const summary = record && presentObligation(record, source).summary;
  if (!summary) return detail;
  const [first, ...rest] = detail.split("\n");
  return [first, `obligation: ${summary}`, ...rest].join("\n");
}
/** One known cause of failure the producer met (`producer --explain`): a
 * form at a source span, and why no derivation of it is found. */
interface Explanation {
  pos: [number, number];
  reason: string;
}
function readExplanations(text: string): Explanation[] {
  try {
    const parsed: unknown = JSON.parse(text);
    if (!Array.isArray(parsed)) return [];
    return parsed.flatMap((e: unknown): Explanation[] =>
      e && typeof e === "object" && "pos" in e && "reason" in e && typeof e.reason === "string" &&
        Array.isArray(e.pos) && e.pos.length === 2 && typeof e.pos[0] === "number" && typeof e.pos[1] === "number"
        ? [{ pos: [e.pos[0], e.pos[1]], reason: e.reason }] : []);
  } catch {
    return [];
  }
}
/** A search that found no derivation, or a quantified call it could not show
 * within its bound, is refused by name where its cause is
 * known, on a first line of its own before the verifier's, which follow
 * unchanged: the producer's explanation of a form at the failed obligation
 * (the innermost whose span meets the obligation's), else, for code
 * TypeScript refuses, where the caller asks for it (`--typescript-errors`: it
 * loads the project again, a second of CPU), the TypeScript error nearest
 * the failed obligation: the
 * pipeline follows TypeScript's types, and SKJS accepting what TypeScript
 * refuses is SKJS going beyond them (the repository's AGENTS.md, "Match
 * TypeScript"). Display only: the outcome is the same unverified search,
 * which Lean decided on the ordinary proposal. */
function refusedByName(detail: string, explain: () => Explanation[],
    read: () => SeenDiagnostic[]): string {
  if (!detail.includes("evidence search failed") &&
      !detail.includes("does not satisfy the closure's bound")) return detail;
  const at = /at \[(\d+),(\d+)\)/.exec(detail);
  if (at) {
    const [start, end] = [Number(at[1]), Number(at[2])];
    const meets = explain().filter((e) => e.pos[0] < Math.max(end, start + 1) && start < e.pos[1])
      .sort((a, b) => (a.pos[1] - a.pos[0]) - (b.pos[1] - b.pos[0]));
    if (meets.length) return `reject: ${meets[0].reason}\n${detail}`;
  }
  const errors = read();
  if (!errors.length) return detail;
  const pos = at ? Number(at[1]) : 0;
  const distance = (d: SeenDiagnostic) =>
    pos < d.pos[0] ? d.pos[0] - pos : pos > d.pos[1] ? pos - d.pos[1] : 0;
  const nearest = errors.reduce((a, b) => (distance(b) < distance(a) ? b : a));
  const text = nearest.text.split("\n")[0];
  return `reject: TypeScript refuses this code too (line ${nearest.start.line + 1}, col ${
    nearest.start.character + 1}: ${text}); the pipeline follows TypeScript's types\n${detail}`;
}
function typeScriptErrors(file: string, tsconfigPath?: string): SeenDiagnostic[] {
  try {
    return clientErrors(file, tsconfigPath);
  } catch {
    return [];
  }
}
/** Acceptance is deliberately private to this module. An OCaml proposal alone
 * cannot construct the public verified outcome: both Lean phases must succeed. */
export function check(source: string, tsconfigPath?: string, typescriptErrors = false): Outcome {
  const artifacts = mkdtempSync(join(tmpdir(), "ocaml-producer-"));
  let phase: Phase = "source";
  try {
    // Parse a snapshot, not a path whose contents may change during verification.
    const snapshot = join(artifacts, "source.ts");
    const bytes = readFileSync(resolve(source));
    writeFileSync(snapshot, bytes);
    writeFileSync(
      join(artifacts, "tsconfig.json"),
      JSON.stringify({
        compilerOptions: { strict: true, noEmit: true, target: "es2022" },
        files: ["source.ts"],
      }),
    );
    // A caller may name the TypeScript project the source belongs to. The
    // snapshot is parsed, and TypeScript resolves its imports as the original
    // file in that project; the parser requires both to have the same bytes.
    // The producer and verifier still decide whether they can interpret the
    // declarations reached.
    // The TypeScript errors the parser's gate read are kept beside its log,
    // accepted or not: they are where a refusal over one of them points.
    const diagnostics = join(artifacts, "typescript-diagnostics.json");
    const parsed = tsconfigPath
      ? (() => {
          const seen: SeenDiagnostic[] = [];
          try {
            return { code: 0, out: JSON.stringify(parseFile(snapshot, false, tsconfigPath, resolve(source),
              (d) => seen.push(d))), detail: "" };
          } catch (error) {
            return { code: 1, out: "", detail: error instanceof Error ? error.message : String(error) };
          } finally {
            writeFileSync(diagnostics, JSON.stringify(seen, null, 1) + "\n");
          }
        })()
      : run(process.execPath, [
          resolve(repo, "verification/tools/fragment-parse.mts"),
          snapshot,
          "--typescript-diagnostics",
          diagnostics,
        ]);
    writeFileSync(join(artifacts, "parse.log"), parsed.detail);
    if (parsed.code !== 0)
      return {
        status: parsed.detail.startsWith("gate:") ? "unsupported" : "error",
        artifacts,
        phase,
        detail: parsed.detail,
      };
    const ast = join(artifacts, "fragment.json");
    writeFileSync(ast, parsed.out);
    const parsedData: unknown = JSON.parse(parsed.out);
    if (
      !parsedData ||
      typeof parsedData !== "object" ||
      !("sourceSha256" in parsedData) ||
      parsedData.sourceSha256 !==
        createHash("sha256").update(bytes).digest("hex")
    )
      throw Error("parser fingerprint differs from source snapshot");
    if (!("functions" in parsedData) || !Array.isArray(parsedData.functions))
      throw Error("parser omitted functions");
    const functions = parsedData.functions.map((f: unknown) => {
      if (
        !f ||
        typeof f !== "object" ||
        !("name" in f) ||
        typeof f.name !== "string"
      )
        throw Error("invalid function identity");
      return f.name;
    });
    if (!("init" in parsedData) || !Array.isArray(parsedData.init))
      throw Error("parser omitted the module initialization");
    const initialization = parsedData.init.map((s: unknown): [number, number] => {
      if (!s || typeof s !== "object" || !("pos" in s) || !Array.isArray(s.pos) ||
          s.pos.length !== 2 || !s.pos.every((n: unknown) => typeof n === "number"))
        throw Error("invalid initialization statement position");
      return [s.pos[0], s.pos[1]];
    });
    phase = "proposal";
    const proposed = run(join(here, "_build/default/producer.exe"), [ast]);
    writeFileSync(join(artifacts, "proposal.log"), proposed.detail);
    if (proposed.code !== 0)
      return {
        status: proposed.detail.startsWith("unsupported:")
          ? "unsupported"
          : "error",
        artifacts,
        phase,
        detail: proposed.detail,
      };
    const claims = join(artifacts, "claims.json"),
      evidence = join(artifacts, "evidence.json");
    writeFileSync(claims, proposed.out);
    phase = "search";
    const produced = run(verifier, [
      "--produce-source-claims",
      ast,
      claims,
      snapshot,
      evidence,
      String(searchDepth),
    ]);
    writeFileSync(join(artifacts, "search.log"), produced.detail);
    if (produced.code !== 0)
      return {
        status: "unverified",
        artifacts,
        phase,
        detail: refusedByName(namingTheObligation(produced.detail, bytes.toString("utf8")),
          () => readExplanations(run(join(here, "_build/default/producer.exe"), ["--explain", ast]).out),
          () => typescriptErrors ? typeScriptErrors(tsconfigPath ? resolve(source) : snapshot, tsconfigPath) : []),
      };
    phase = "check";
    const checked = run(verifier, [
      "--check-source-claims",
      ast,
      claims,
      snapshot,
      evidence,
    ]);
    writeFileSync(join(artifacts, "check.log"), checked.detail);
    if (checked.code !== 0)
      return { status: "unverified", artifacts, phase, detail: checked.detail };
    return { status: "verified", artifacts, phase, functions, initialization };
  } catch (e) {
    return {
      status: "error",
      artifacts,
      phase,
      detail: e instanceof Error ? e.message : String(e),
    };
  }
}
/** The same run in a process of its own, exactly as the command line below
 * runs it, for a caller that must stay responsive or runs several at once.
 * `project` is what `--project` takes; `typescriptErrors`, whether a failed
 * search is named by TypeScript's errors (`--typescript-errors`). */
export function checkApart(source: string, project?: string, typescriptErrors = false): Promise<Outcome> {
  const args = [import.meta.filename, source, ...(project ? ["--project", project] : []),
    ...(typescriptErrors ? ["--typescript-errors"] : [])];
  return new Promise((done, fail) =>
    execFile(process.execPath, args, { cwd: repo, maxBuffer: 16 * 1024 * 1024 }, (_error, stdout, stderr) => {
      // A source that is not verified exits 1 and still prints its outcome.
      try {
        done(JSON.parse(stdout) as Outcome);
      } catch {
        fail(new Error(`no outcome: ${stderr.trim()}`));
      }
    }));
}
if (process.argv[1] && resolve(process.argv[1]) === import.meta.filename) {
  const all = process.argv.slice(2);
  const typescriptErrors = all.includes("--typescript-errors");
  const args = all.filter((a) => a !== "--typescript-errors");
  if (!(args.length === 1 || (args.length === 3 && args[1] === "--project"))) {
    process.stderr.write("usage: node check.mts file.ts [--project tsconfig-or-directory] [--typescript-errors]\n");
    process.exitCode = 2;
  } else {
    try {
      const result = check(args[0], args[2] ? tsconfigOf(args[2]) : undefined, typescriptErrors);
      process.stdout.write(JSON.stringify(result, null, 2) + "\n");
      process.exitCode = result.status === "verified" ? 0 : 1;
    } catch (error) {
      process.stderr.write((error instanceof Error ? error.message : String(error)) + "\n");
      process.exitCode = 1;
    }
  }
}
