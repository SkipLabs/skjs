import { spawnSync } from "node:child_process";
import { mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { resolve, join } from "node:path";
import { createHash } from "node:crypto";
import { parseFile, type ImportUniverse } from "../tools/fragment-parse.mts";
import { loadImportUniverseFromProject } from "../tools/import-universe-project.mts";

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
      phase: "check";
    }
  | {
      status: "unsupported" | "unverified" | "error";
      artifacts: string;
      detail: string;
      phase: Phase;
    };
function run(command: string, args: string[]) {
  const p = spawnSync(command, args, {
    cwd: repo,
    encoding: "utf8",
    timeout: 30_000,
    maxBuffer: 16 * 1024 * 1024,
  });
  if (p.error || p.signal || p.status === null)
    throw Error(
      `${command}: ${p.error?.message ?? p.signal ?? "no exit status"}`,
    );
  return {
    code: p.status,
    out: p.stdout,
    detail: p.stderr.trim() || p.stdout.trim(),
  };
}
/** Acceptance is deliberately private to this module. An OCaml proposal alone
 * cannot construct the public verified outcome: both Lean phases must succeed. */
export function check(source: string, importUniverse?: ImportUniverse): Outcome {
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
    // A caller may supply an explicit module universe. Its resolved, hashed
    // source closure is carried in the Fragment; the producer and verifier
    // still decide independently whether they can interpret it.
    const parsed = importUniverse
      ? (() => {
          try {
            return { code: 0, out: JSON.stringify(parseFile(snapshot, false, importUniverse)), detail: "" };
          } catch (error) {
            return { code: 1, out: "", detail: error instanceof Error ? error.message : String(error) };
          }
        })()
      : run(process.execPath, [
          resolve(repo, "verification/tools/fragment-parse.mts"),
          snapshot,
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
      "12",
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
    return { status: "verified", artifacts, phase, functions };
  } catch (e) {
    return {
      status: "error",
      artifacts,
      phase,
      detail: e instanceof Error ? e.message : String(e),
    };
  }
}
if (process.argv[1] && resolve(process.argv[1]) === import.meta.filename) {
  const args = process.argv.slice(2);
  if (!(args.length === 1 || (args.length === 3 && args[1] === "--project"))) {
    process.stderr.write("usage: node check.mts file.ts [--project source-tree]\n");
    process.exitCode = 2;
  } else {
    try {
      const result = check(args[0], args[2] ? loadImportUniverseFromProject(args[2]) : undefined);
      process.stdout.write(JSON.stringify(result, null, 2) + "\n");
      process.exitCode = result.status === "verified" ? 0 : 1;
    } catch (error) {
      process.stderr.write((error instanceof Error ? error.message : String(error)) + "\n");
      process.exitCode = 1;
    }
  }
}
