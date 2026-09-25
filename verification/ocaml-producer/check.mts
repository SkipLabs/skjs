import { execFile, spawnSync } from "node:child_process";
import { mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { basename, resolve, join } from "node:path";
import { createHash } from "node:crypto";
import { parseFile } from "../tools/fragment-parse.mts";
import { tsconfigOf, type SeenDiagnostic } from "../tools/declaration-graph.mts";

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
/** Acceptance is deliberately private to this module. An OCaml proposal alone
 * cannot construct the public verified outcome: both Lean phases must succeed. */
export function check(source: string, tsconfigPath?: string): Outcome {
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
        detail: produced.detail,
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
 * `project` is what `--project` takes. */
export function checkApart(source: string, project?: string): Promise<Outcome> {
  const args = [import.meta.filename, source, ...(project ? ["--project", project] : [])];
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
  const args = process.argv.slice(2);
  if (!(args.length === 1 || (args.length === 3 && args[1] === "--project"))) {
    process.stderr.write("usage: node check.mts file.ts [--project tsconfig-or-directory]\n");
    process.exitCode = 2;
  } else {
    try {
      const result = check(args[0], args[2] ? tsconfigOf(args[2]) : undefined);
      process.stdout.write(JSON.stringify(result, null, 2) + "\n");
      process.exitCode = result.status === "verified" ? 0 : 1;
    } catch (error) {
      process.stderr.write((error instanceof Error ? error.message : String(error)) + "\n");
      process.exitCode = 1;
    }
  }
}
