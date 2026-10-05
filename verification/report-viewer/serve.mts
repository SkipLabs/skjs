#!/usr/bin/env node
"use strict";

import http from "node:http";
import fs from "node:fs/promises";
import path from "node:path";
import os from "node:os";
import crypto from "node:crypto";
import { spawn } from "node:child_process";
import { execFile as execFileCb } from "node:child_process";
import { promisify } from "node:util";
import type { Bundle, PipelineOutcome } from "./types.ts";
import { fieldOf, messageOf, outputOf } from "../tools/thrown.mts";
import { cases } from "../pipeline/cases.mts";
import { checkApart, searchDepth } from "../pipeline/verify-source.mts";
import { typescriptVerdicts } from "../tools/fragment-parse.mts";
import { tsconfigOf, type SeenDiagnostic } from "../tools/declaration-graph.mts";

/** What the child processes below are run with, decided once. */
interface RunOptions {
  cwd: string;
  timeout: number;
  maxBuffer: number;
}

const execFile = promisify(execFileCb);
const __dirname = path.dirname(import.meta.filename);

const REPO = path.resolve(
  process.env.SKJS_REPO || path.join(__dirname, "../.."),
);
const VERIFIER = "verification/lean/.lake/build/bin/verifier";
const PORT = Number(process.env.PORT || 8731);
const EXAMPLES = "./corpus-index.mts";
// Read the example groups per request: editing that list should show up on the
// next page load, not only after restarting this server. A module is cached by
// its specifier, so a fresh one is asked for each time.
async function exampleGroups() {
  return import(`${EXAMPLES}?at=${Date.now()}`);
}

// Any repository source can be opened, so the picker is a starting point rather
// than the limit. The listing is cached briefly: it is a convenience for finding
// a path, and it never widens what `repositoryPath` allows.
const SKIP = new Set([
  "node_modules",
  "target",
  "dist",
  "build",
  "out",
  ".git",
  ".lake",
  ".cache",
]);
let listing: { at: number; files: string[] } = { at: 0, files: [] };
async function sources() {
  if (Date.now() - listing.at < 10000) return listing.files;
  const files: string[] = [];
  const walk = async (dir: string) => {
    if (files.length > 20000) return;
    let entries;
    try {
      entries = await fs.readdir(dir, { withFileTypes: true });
    } catch {
      return;
    }
    for (const entry of entries) {
      if (entry.name.startsWith(".") || SKIP.has(entry.name)) continue;
      const full = path.join(dir, entry.name);
      if (entry.isDirectory()) await walk(full);
      // A claim source is a `.ts` the parser accepts. The `.mts` beside it is
      // this repository's own tooling, which the gate would reject anyway.
      else if (/\.(ts|tsx)$/.test(entry.name) && !entry.isSymbolicLink())
        files.push(path.relative(REPO, full));
    }
  };
  await walk(REPO);
  files.sort();
  listing = { at: Date.now(), files };
  return files;
}

async function repositoryPath(relative: string) {
  const resolved = await fs
    .realpath(path.resolve(REPO, relative))
    .catch(() => {
      throw new Error(
        `No such file in the repository: ${relative || "(no path given)"}`,
      );
    });
  if (!resolved.startsWith((await fs.realpath(REPO)) + path.sep))
    throw new Error("Path outside the repository");
  return resolved;
}

async function hasVerifier() {
  return fs.access(path.join(REPO, VERIFIER)).then(
    () => true,
    () => false,
  );
}

/*
 * What the report viewer shows is one run of the pipeline, `verify-source.mts`, the same run
 * its suites and the corpus judge. The page is built from what
 * that run left in its artifacts — the source snapshot, the Fragment the shared
 * parser wrote, the claims the producer proposed, the evidence the verifier
 * checked, and the TypeScript errors the parser's gate read. Nothing is parsed
 * or proposed again here, so a file the pipeline runs is a file the report viewer
 * shows, and what it shows as the outcome is the pipeline's.
 * Verification is not an option the caller turns on: if a verifier is present
 * it runs, so what is displayed is always checked against the claims on screen.
 */

/**
 * The TypeScript errors a run's gate read in the checked source, in the one
 * diagnostics text the page places under the spans it names (`--diagnostics`),
 * named by the source's own path: the run read a snapshot of it. The run also
 * keeps what it read in the files the source imports, which are not this
 * page's; a refusal over one of those names it in the outcome.
 */
async function typescriptDiagnostics(artifacts: string, relative: string) {
  const seen: SeenDiagnostic[] = JSON.parse(
    await fs
      .readFile(path.join(artifacts, "typescript-diagnostics.json"), "utf8")
      .catch(() => "[]"),
  );
  return seen
    .filter((d) => d.client)
    .map((d) => {
      // The page places a diagnostic on its first line, with 1-based columns
      // and an exclusive end.
      const to =
        d.end.line === d.start.line ? d.end.character : d.start.character + 1;
      return (
        `File "${relative}", line ${d.start.line + 1}, ` +
        `character ${d.start.character + 1}-${to + 1}:\n` +
        `TypeScript: ${d.text}\n`
      );
    })
    .join("");
}

async function pipelineAnalyse(
  relative: string,
  source: string,
  tmp: string,
  options: RunOptions,
): Promise<Bundle> {
  const startedAt = Date.now();
  // A fixture that names its project is run in it, as its case is.
  const project = cases.find(
    (c) => relative === `verification/pipeline/examples/${c.file}.ts`,
  )?.project;
  const outcome = await checkApart(relative, project && path.join(REPO, project));
  try {
    const at = (name: string) => path.join(outcome.artifacts, name);
    // The page shows the bytes the pipeline checked, and they are the file's.
    const snapshot = await fs.readFile(at("source.ts"), "utf8");
    if (
      snapshot !== source ||
      source !== (await fs.readFile(await repositoryPath(relative), "utf8"))
    )
      throw new Error("Source changed during collection; run again");
    const digest = crypto.createHash("sha256").update(source).digest("hex");
    const diagnostics = await typescriptDiagnostics(outcome.artifacts, relative);
    const shown: PipelineOutcome =
      outcome.status === "verified"
        ? { status: outcome.status, phase: outcome.phase, functions: outcome.functions }
        : { status: outcome.status, phase: outcome.phase, detail: outcome.detail };
    const collection = (verified: boolean) => ({
      command: "verify-source.mts " + relative + (project ? " --project " + project : ""),
      ranAt: new Date(startedAt).toISOString(),
      durationMs: Date.now() - startedAt,
      verified,
    });
    const proposed = await fs
      .readFile(at("claims.json"), "utf8")
      .catch(() => null);
    // Refused before any claim was proposed: the source, under that outcome,
    // with what TypeScript said where it said it.
    if (proposed === null)
      return {
        source,
        manifest: {
          source: { file: relative, sha256: digest },
          functions: [],
          gaps: [],
          results: null,
          missingFunctions: [],
          diagnostics,
        },
        collection: collection(false),
        outcome: shown,
      };
    // The run named its snapshot; the page names the file it is a snapshot
    // of, which the digests above say it is.
    const claims = { ...JSON.parse(proposed), file: relative };
    const claimsPath = path.join(tmp, "claims.json");
    await fs.writeFile(claimsPath, JSON.stringify(claims));
    const fragmentPath = path.join(tmp, "fragment.json");
    await fs.writeFile(
      fragmentPath,
      JSON.stringify({
        ...JSON.parse(await fs.readFile(at("fragment.json"), "utf8")),
        file: relative,
      }),
    );
    const args = [
      "verification/tools/annotate-source.mts",
      relative,
      "--claims",
      claimsPath,
      "--fragment",
      fragmentPath,
      "--depth",
      String(searchDepth),
      "--stdout",
      "json",
    ];
    if (diagnostics) {
      const written = path.join(tmp, "diagnostics.txt");
      await fs.writeFile(written, diagnostics);
      args.push("--diagnostics", written);
    }
    // Verified, the functions are verified by the evidence the run checked;
    // otherwise each is checked alone over the same Fragment and claims, to
    // say where the run's search stopped.
    const verify = await hasVerifier();
    if (verify) args.push("--verify", VERIFIER);
    if (verify && outcome.status === "verified")
      args.push("--evidence", at("evidence.json"));
    const result = await execFile(process.execPath, args, options);
    const bundle = JSON.parse(String(result.stdout));
    if (bundle.manifest.source.sha256 !== digest)
      throw new Error("Report source identity mismatch");
    // TypeScript's own verdict on each function, beside the verifier's, in
    // the project the run checked it in: the case's, or the snapshot's own.
    const verdicts = project
      ? typescriptVerdicts(await repositoryPath(relative), tsconfigOf(path.join(REPO, project)))
      : typescriptVerdicts(at("source.ts"));
    for (const fn of bundle.manifest.functions) {
      const accepted = verdicts.get(fn.name);
      if (accepted !== undefined) fn.typescriptAccepted = accepted;
    }
    return {
      source,
      ...bundle,
      collection: collection(Boolean(verify)),
      outcome: shown,
    };
  } finally {
    await fs.rm(outcome.artifacts, { recursive: true, force: true });
    await fs.rm(tmp, { recursive: true, force: true });
  }
}

async function analyse(relative: string): Promise<Bundle> {
  const source = await fs.readFile(await repositoryPath(relative), "utf8");
  const tmp = await fs.mkdtemp(path.join(os.tmpdir(), "claim-report-"));
  const options = { cwd: REPO, timeout: 120000, maxBuffer: 32 * 1024 * 1024 };
  return pipelineAnalyse(relative, source, tmp, options);
}

// app/index.html is the page the bundle is built from, which loads the application.
// app/vite.config.ts builds that page into `app/dist` under the stable names this table serves.
// The report viewer is a built bundle in `app/dist`, which exists only after
// `npm --prefix app run build`; `make viewer` builds before it serves.
const assets = new Map([
  ["/", ["app/dist/index.html", "text/html"]],
  ["/viewer.js", ["app/dist/viewer.js", "text/javascript"]],
  ["/viewer.css", ["app/dist/viewer.css", "text/css"]],
]);
const send = (
  res: http.ServerResponse,
  status: number,
  data: unknown,
  type = "application/json",
) => {
  res.writeHead(status, {
    "content-type": type + "; charset=utf-8",
    "cache-control": "no-store",
  });
  res.end(type === "application/json" ? JSON.stringify(data) : String(data));
};

// Bound concurrency: expensive runs do not block file loading or health checks.
let analysing = false;
const server = http.createServer(async (req, res) => {
  const url = new URL(req.url ?? "/", "http://localhost");
  try {
    if (url.pathname === "/api/health")
      return send(res, 200, { verifier: await hasVerifier() });
    if (url.pathname === "/api/files") {
      const examples = await exampleGroups();
      // `viewerGroups`, not `groups`: the picker is a way to reach a file, and
      // it also offers the OCaml producer's own fixtures, which are that
      // producer's inventory rather than corpus policy.
      return send(res, 200, {
        files: examples.supported,
        groups: examples.viewerGroups,
      });
    }
    if (url.pathname === "/api/sources") {
      const query = (url.searchParams.get("q") || "").toLowerCase();
      const all = await sources();
      const matched = query
        ? all.filter((f) => f.toLowerCase().includes(query))
        : all;
      return send(res, 200, {
        files: matched.slice(0, 60),
        total: matched.length,
      });
    }
    if (url.pathname === "/api/analyse") {
      if (analysing)
        return send(res, 409, {
          error: "A collection is already running. Try again when it finishes.",
        });
      analysing = true;
      try {
        return send(
          res,
          200,
          await analyse(url.searchParams.get("path") || ""),
        );
      } finally {
        analysing = false;
      }
    }
    const asset = assets.get(url.pathname);
    if (!asset) return send(res, 404, { error: "Not found" });
    return send(
      res,
      200,
      await fs.readFile(path.join(__dirname, asset[0])),
      asset[1],
    );
  } catch (thrown) {
    send(res, 500, {
      error: (outputOf(thrown, "stderr") || messageOf(thrown)).slice(0, 4000),
    });
  }
});
// Only a direct run serves: importing this module for `analyse` must not take
// the port.
if (process.argv[1] && import.meta.filename === path.resolve(process.argv[1])) {
  // A port already taken usually means a report viewer is up from an earlier run.
  // Say so, with what to do about it, rather than a stack trace.
  server.on("error", (error) => {
    if (fieldOf(error, "code") !== "EADDRINUSE") throw error;
    console.error(
      `Port ${PORT} is already serving. Open http://localhost:${PORT},` +
        ` or run on another port with PORT=8732 make viewer.`,
    );
    process.exit(1);
  });
  server.listen(PORT, "127.0.0.1", () => {
    const url = `http://localhost:${PORT}`;
    console.log(`Claim report viewer on ${url}`);
    // `--open` hands the page to the browser once the socket is actually
    // listening, so nothing races the server's start.
    if (process.argv.includes("--open")) {
      // An argument after `--open` names the page to open, so the report viewer being
      // rebuilt can be asked for without a second flag.
      const at = process.argv.indexOf("--open");
      const page = (process.argv[at + 1] || "").startsWith("/")
        ? process.argv[at + 1]
        : "";
      const opener =
        process.platform === "darwin"
          ? "open"
          : process.platform === "win32"
            ? "start"
            : "xdg-open";
      spawn(opener, [url + page], { stdio: "ignore", detached: true })
        .on("error", () => console.log(`Open ${url} to read reports.`))
        .unref();
    }
  });
}

export { analyse };
