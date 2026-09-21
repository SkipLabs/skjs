import { spawnSync } from "node:child_process";
import { mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { resolve, join } from "node:path";
import { createHash } from "node:crypto";

const here = import.meta.dirname;
const repo = resolve(here, "../..");
export const verifier =
  process.env.VERIFIER ??
  resolve(repo, "verification/lean/.lake/build/bin/verifier");
export type Outcome =
  | { status: "verified"; artifacts: string }
  | {
      status: "unsupported" | "unverified" | "error";
      artifacts: string;
      detail: string;
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
export function check(source: string): Outcome {
  const artifacts = mkdtempSync(join(tmpdir(), "ocaml-producer-"));
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
    const parsed = run(process.execPath, [
      resolve(repo, "verification/tools/fragment-parse.mts"),
      snapshot,
    ]);
    writeFileSync(join(artifacts, "parse.log"), parsed.detail);
    if (parsed.code !== 0)
      return { status: "unsupported", artifacts, detail: parsed.detail };
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
    const proposed = run(join(here, "_build/producer"), [ast]);
    writeFileSync(join(artifacts, "proposal.log"), proposed.detail);
    if (proposed.code !== 0)
      return { status: "unsupported", artifacts, detail: proposed.detail };
    const claims = join(artifacts, "claims.json"),
      evidence = join(artifacts, "evidence.json");
    writeFileSync(claims, proposed.out);
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
      return { status: "unverified", artifacts, detail: produced.detail };
    const checked = run(verifier, [
      "--check-source-claims",
      ast,
      claims,
      snapshot,
      evidence,
    ]);
    writeFileSync(join(artifacts, "check.log"), checked.detail);
    if (checked.code !== 0)
      return { status: "unverified", artifacts, detail: checked.detail };
    return { status: "verified", artifacts };
  } catch (e) {
    return {
      status: "error",
      artifacts,
      detail: e instanceof Error ? e.message : String(e),
    };
  }
}
if (process.argv[1] && resolve(process.argv[1]) === import.meta.filename) {
  const source = process.argv[2];
  if (!source) {
    process.stderr.write("usage: node check.mts file.ts\n");
    process.exitCode = 2;
  } else {
    const result = check(source);
    process.stdout.write(JSON.stringify(result, null, 2) + "\n");
    process.exitCode = result.status === "verified" ? 0 : 1;
  }
}
