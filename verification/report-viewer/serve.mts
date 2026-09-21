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
import type { Bundle, Candidate } from "./types.ts";
import { fieldOf, messageOf, outputOf } from "../tools/thrown.mts";

/** What the page posts: the candidate to check or keep, and — for a draft —
 * what to do with it. Discarding one names the source alone, and everything
 * here arrives from a browser, so nothing is assumed of it. */
interface CandidateRequest {
  candidate?: Candidate;
  file?: string;
  remove?: boolean;
}

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
const EXAMPLES = "./examples.mts";
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

/*
 * A draft lives beside the source it is about, named after it, the way the
 * command-line tools already name what they write. It is meaningful for that
 * file and no other — its `sourceSha256` must match — so there is nothing to
 * choose and nothing to find: opening the source finds its draft.
 *
 * What is written is the candidate itself, not a display bundle, so the same
 * file can be handed to `annotate-source.mts --claims`.
 */
const draftPath = (source: string) => source.replace(/\.tsx?$/, "") + ".candidate.json";

/**
 * The draft beside a source. A draft is about one exact source, so one written
 * before that source changed describes text that is no longer there and cannot
 * be shown — but saying nothing would leave a file in the tree that silently
 * does nothing, so what is wrong with it is reported instead.
 */
async function readDraft(absolute: string, sourceSha256: string) {
  const at = draftPath(absolute);
  const text = await fs.readFile(at, "utf8").catch(() => null);
  if (text === null) return null;
  const named = path.relative(REPO, at);
  let draft;
  try {
    draft = JSON.parse(text);
  } catch {
    return { stale: `${named} is not readable as a candidate` };
  }
  if (draft?.sourceSha256 !== sourceSha256)
    return {
      stale:
        `${named} was written before this source changed, ` +
        `so it is not shown`,
    };
  return { draft };
}

/**
 * The producers the reader can ask for, each a collector below. A query string
 * arrives from a browser, so a name that is not one of these names nothing to
 * run and reads as the default rather than being passed on.
 */
const PRODUCERS = new Set(["skjs", "tsc", "ocaml"]);
const producerAsked = (asked: string | null) =>
  asked && PRODUCERS.has(asked) ? asked : "skjs";

async function hasVerifier() {
  return fs.access(path.join(REPO, VERIFIER)).then(
    () => true,
    () => false,
  );
}

// Verification is not an option the caller turns on: if a verifier is present it
// runs, so what is displayed is always checked against the claims on screen.
// The other producer: what TypeScript's own checker claims at the same sites,
// through the same verifier, including primitive field assertions at direct
// statement-entry reads. tests/tsc-claims/README.md records its limits.
async function tscAnalyse(
  relative: string,
  source: string,
  tmp: string,
  options: RunOptions,
): Promise<Bundle> {
  const startedAt = Date.now();
  try {
    const claims = path.join(tmp, "tsc-claims.mtson");
    await execFile(
      process.execPath,
      ["verification/tools/tsc-claims.mts", relative, "--out", claims],
      options,
    );
    const args = [
      "verification/tools/annotate-source.mts",
      relative,
      "--claims",
      claims,
      "--producer",
      "tsc",
      "--format",
      "source-claims",
      "--stdout",
      "json",
    ];
    const verify = await hasVerifier();
    if (verify) args.push("--verify", VERIFIER);
    const result = await execFile(process.execPath, args, options);
    const bundle = JSON.parse(String(result.stdout));
    const outcomes = JSON.parse(await fs.readFile(claims + ".outcomes.json", "utf8"));
    for (const fn of bundle.manifest.functions) {
      if (typeof outcomes[fn.name] === "boolean") fn.collection = {
        completion: outcomes[fn.name] ? "complete" : "aborted",
        quality: "unverified", mode: "normal",
      };
    }
    const digest = crypto
      .createHash("sha256")
      .update(source)
      .digest("hex");
    if (bundle.manifest.source.sha256 !== digest)
      throw new Error("Report source identity mismatch");
    return {
      source,
      ...bundle,
      collection: {
        producer: "tsc",
        producerRun: true,
        command: "tsc-claims.mts " + relative,
        ranAt: new Date(startedAt).toISOString(),
        durationMs: Date.now() - startedAt,
        verified: Boolean(verify),
      },
      candidate: {
        format: "source-claims",
        file: relative,
        sourceSha256: digest,
        claims: JSON.parse(await fs.readFile(claims, "utf8")),
      },
    };
  } finally {
    await fs.rm(tmp, { recursive: true, force: true });
  }
}

/*
 * The third producer: an independent OCaml implementation of claim inference.
 * It reads the same Fragment the shared parser writes and emits the same
 * SourceClaims document the SKJS export is converted into, so the same verifier
 * adjudicates it and nothing here is a second opinion about what a claim means.
 * `ocaml-producer/README.md` records what it implements; a source outside that
 * is refused by name rather than collected as a report with nothing in it.
 */
const OCAML = "verification/ocaml-producer/_build/default/producer.exe";

/**
 * What a child wrote before failing, as the reason to show. The shared parser
 * and the OCaml producer both name their own limits on stderr — `gate: …` and
 * `unsupported: …` — and those are statements about the source, so they are
 * reported in their own words rather than as a stack trace.
 */
const refusal = (thrown: unknown, what: string) =>
  new Error(
    `${what}: ${(outputOf(thrown, "stderr") || messageOf(thrown)).trim()}`,
  );

async function ocamlAnalyse(
  relative: string,
  source: string,
  tmp: string,
  options: RunOptions,
): Promise<Bundle> {
  const startedAt = Date.now();
  try {
    const producer = path.join(REPO, OCAML);
    // Its build is not this server's to run: an absent executable says which
    // command builds it, rather than failing as a missing file somewhere.
    if (!(await fs.access(producer).then(() => true, () => false)))
      throw new Error(
        `${OCAML} is not built. Build it with: ` +
          "dune build --root verification/ocaml-producer",
      );
    // The producer consumes the Fragment, never the source text: the shared
    // parser stays the one front end, and its refusals are the fragment's.
    let parsed;
    try {
      parsed = await execFile(
        process.execPath,
        ["verification/tools/fragment-parse.mts", relative],
        options,
      );
    } catch (thrown) {
      throw refusal(thrown, "The shared parser refused this source");
    }
    const fragment = path.join(tmp, "fragment.json");
    await fs.writeFile(fragment, parsed.stdout);
    let proposed;
    try {
      proposed = await execFile(producer, [fragment], options);
    } catch (thrown) {
      throw refusal(thrown, "The OCaml producer proposed no claims");
    }
    const claims = path.join(tmp, "claims.json");
    await fs.writeFile(claims, proposed.stdout);
    const args = [
      "verification/tools/annotate-source.mts",
      relative,
      "--claims",
      claims,
      "--producer",
      "ocaml",
      "--format",
      "source-claims",
      "--stdout",
      "json",
    ];
    // Whatever either step said while still succeeding, under the spans it
    // names — the same place the SKJS producer's own errors are shown.
    const said = ((parsed.stderr ?? "") + (proposed.stderr ?? "")).trim();
    if (said) {
      const diagnostics = path.join(tmp, "diagnostics.txt");
      await fs.writeFile(diagnostics, said + "\n");
      args.push("--diagnostics", diagnostics);
    }
    const verify = await hasVerifier();
    if (verify) args.push("--verify", VERIFIER);
    const result = await execFile(process.execPath, args, options);
    const bundle = JSON.parse(String(result.stdout));
    if (source !== (await fs.readFile(await repositoryPath(relative), "utf8")))
      throw new Error("Source changed during collection; run again");
    const digest = crypto.createHash("sha256").update(source).digest("hex");
    if (bundle.manifest.source.sha256 !== digest)
      throw new Error("Report source identity mismatch");
    return {
      source,
      ...bundle,
      collection: {
        producer: "ocaml",
        producerRun: true,
        command: OCAML + " (fragment of " + relative + ")",
        ranAt: new Date(startedAt).toISOString(),
        durationMs: Date.now() - startedAt,
        verified: Boolean(verify),
      },
      candidate: {
        format: "source-claims",
        file: relative,
        sourceSha256: digest,
        claims: JSON.parse(await fs.readFile(claims, "utf8")),
      },
    };
  } finally {
    await fs.rm(tmp, { recursive: true, force: true });
  }
}

async function analyse(relative: string, producer = "skjs"): Promise<Bundle> {
  const bundle = await collect(relative, producer);
  // The draft, where one is beside the source and is about this source. The
  // reader decides what to do with it; the server only reports that it exists.
  const kept = await readDraft(
    await repositoryPath(relative),
    bundle.manifest?.source?.sha256,
  );
  return kept ? { ...bundle, ...kept } : bundle;
}

async function collect(relative: string, producer = "skjs"): Promise<Bundle> {
  const sourcePath = await repositoryPath(relative);
  const source = await fs.readFile(sourcePath, "utf8");
  const tmp = await fs.mkdtemp(path.join(os.tmpdir(), "claim-report-"));
  const options = { cwd: REPO, timeout: 120000, maxBuffer: 32 * 1024 * 1024 };
  if (producer === "tsc") return tscAnalyse(relative, source, tmp, options);
  if (producer === "ocaml")
    return ocamlAnalyse(relative, source, tmp, options);
  // Every request runs the producer: nothing here is cached or reused. The
  // reader shows when it ran, so a displayed report is never mistaken for an
  // older one.
  const startedAt = Date.now();
  try {
    let run: { stdout: string; stderr?: string };
    try {
      run = await execFile(
        "docker",
        [
          "run",
          "--rm",
          "-v",
          REPO + ":/work/skjs",
          "-v",
          path.resolve(REPO, "../skip") + ":/work/skip",
          "-w",
          "/work/skjs",
          process.env.SKJS_IMAGE || "skiplabs/skip:latest",
          process.env.SKJS_BIN || "target/host/dev/skjs",
          "check",
          "--import-stubs",
          "import-stubs",
          "--truthiness",
          "boolean",
          "--emit-skjs-type-claims",
          relative,
        ],
        options,
      );
    } catch (thrown) {
      // Normal rejection can still yield a partial collection. Operational
      // errors cannot, and a thrown value is unknown until something checks it.
      if (
        fieldOf(thrown, "killed") ||
        typeof fieldOf(thrown, "code") !== "number" ||
        !outputOf(thrown, "stdout").trim().startsWith("[")
      )
        throw thrown;
      // The producer refused the program and still wrote its claims.
      run = { stdout: outputOf(thrown, "stdout") };
    }
    const nativeClaims = path.join(tmp, "native-claims.json");
    await fs.writeFile(nativeClaims, run.stdout);
    const claims = path.join(tmp, "claims.json");
    await execFile(process.execPath,["verification/tools/export-source-claims.mts",
      relative,"--claims",nativeClaims,"--out",claims],options);
    const args = [
      "verification/tools/annotate-source.mts",
      relative,
      "--claims",
      claims,
      "--producer",
      "skjs",
      "--format",
      "source-claims",
      "--conversion",
      claims + ".conversion.json",
      "--stdout",
      "json",
    ];
    if ((run.stderr ?? "").trim()) {
      const diagnostics = path.join(tmp, "diagnostics.txt");
      await fs.writeFile(diagnostics, (run.stderr ?? ""));
      args.push("--diagnostics", diagnostics);
    }
    const verify = await hasVerifier();
    if (verify) args.push("--verify", VERIFIER);
    const result = await execFile(process.execPath, args, options);
    const bundle = JSON.parse(result.stdout);
    if (source !== (await fs.readFile(sourcePath, "utf8")))
      throw new Error("Source changed during collection; run again");
    const digest = crypto
      .createHash("sha256")
      .update(source)
      .digest("hex");
    if (bundle.manifest.source.sha256 !== digest)
      throw new Error("Report source identity mismatch");
    return {
      source,
      ...bundle,
      collection: {
        producer: "skjs",
        producerRun: true,
        command:
          (process.env.SKJS_BIN || "target/host/dev/skjs") +
          " check --emit-skjs-type-claims " +
          relative,
        ranAt: new Date(startedAt).toISOString(),
        durationMs: Date.now() - startedAt,
        verified: Boolean(verify),
      },
      candidate: {
        format: "source-claims",
        file: relative,
        sourceSha256: digest,
        claims: JSON.parse(await fs.readFile(claims,"utf8")),
      },
    };
  } finally {
    await fs.rm(tmp, { recursive: true, force: true });
  }
}

// `verify` exists for callers that want attachment validation on its own; the
// HTTP route never passes it, so nothing a browser asks for skips checking.
async function candidateReport(
  candidate: Candidate | undefined,
  verify = true,
): Promise<Bundle> {
  const startedAt = Date.now();
  if (
    !candidate ||
    !["skjs", "source-claims"].includes(candidate.format) ||
    typeof candidate.file !== "string"
  )
    throw new Error("Unsupported candidate format");
  const sourcePath = await repositoryPath(candidate.file);
  const source = await fs.readFile(sourcePath, "utf8");
  const digest = crypto
    .createHash("sha256")
    .update(source)
    .digest("hex");
  if (digest !== candidate.sourceSha256)
    throw new Error(
      "Source changed since this candidate was collected; reload before editing",
    );
  const tmp = await fs.mkdtemp(path.join(os.tmpdir(), "claim-candidate-"));
  try {
    const claims = path.join(tmp, "candidate.json");
    await fs.writeFile(claims, JSON.stringify(candidate.claims));
    const args = [
      "verification/tools/annotate-source.mts",
      candidate.file,
      "--claims",
      claims,
      "--format",
      candidate.format,
      "--producer",
      "manual candidate",
      "--stdout",
      "json",
    ];
    if (verify) {
      if (!(await hasVerifier())) throw new Error("Verifier unavailable");
      args.push("--verify", VERIFIER);
    }
    const result = await execFile(process.execPath, args, {
      cwd: REPO,
      timeout: 120000,
      maxBuffer: 32 * 1024 * 1024,
    });
    if (source !== (await fs.readFile(sourcePath, "utf8")))
      throw new Error("Source changed while checking candidate");
    // The producer is not run here: this report is the edited candidate.
    return {
      source,
      ...JSON.parse(result.stdout),
      collection: {
        producer: "edited candidate",
        producerRun: false,
        ranAt: new Date(startedAt).toISOString(),
        durationMs: Date.now() - startedAt,
        verified: Boolean(verify),
      },
      candidate,
    };
  } finally {
    await fs.rm(tmp, { recursive: true, force: true });
  }
}

async function readCandidate(
  req: http.IncomingMessage,
): Promise<CandidateRequest> {
  if (
    req.method !== "POST" ||
    !req.headers["content-type"]?.startsWith("application/json")
  )
    throw new Error("Candidate checks require a JSON POST");
  const origin = req.headers.origin;
  if (origin && origin !== `http://${req.headers.host}`)
    throw new Error("Cross-origin candidate requests are not allowed");
  const chunks = [];
  let size = 0;
  for await (const chunk of req) {
    size += chunk.length;
    if (size > 16 * 1024 * 1024) throw new Error("Candidate exceeds 16 MiB");
    chunks.push(chunk);
  }
  return JSON.parse(Buffer.concat(chunks).toString("utf8"));
}

// The reader is a built bundle in `app/dist`, which exists only after
// `npm --prefix app run build`; `make viewer` builds before it serves.
const assets = new Map([
  ["/", ["app/dist/index.html", "text/html"]],
  ["/reader.js", ["app/dist/reader.js", "text/javascript"]],
  ["/reader.css", ["app/dist/reader.css", "text/css"]],
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
          await analyse(
            url.searchParams.get("path") || "",
            producerAsked(url.searchParams.get("producer")),
          ),
        );
      } finally {
        analysing = false;
      }
    }
    /*
     * Keeping a draft, or discarding it. This writes into the working tree, so
     * it happens only when asked: applying an edit checks it and writes
     * nothing. What is written is the candidate itself, beside the source and
     * named after it, so the same file can be passed to `annotate-source.mts`.
     */
    if (url.pathname === "/api/draft") {
      const input = await readCandidate(req);
      const file = input.candidate?.file ?? input.file;
      if (typeof file !== "string")
        return send(res, 400, { error: "A draft names the source it is about" });
      const at = draftPath(await repositoryPath(file));
      if (input.remove) {
        await fs.rm(at, { force: true });
        return send(res, 200, { path: path.relative(REPO, at), kept: false });
      }
      const candidate = input.candidate;
      if (
        !candidate ||
        !["skjs", "source-claims"].includes(candidate.format) ||
        typeof candidate.sourceSha256 !== "string"
      )
        return send(res, 400, { error: "Unsupported candidate" });
      const source = await fs.readFile(await repositoryPath(file), "utf8");
      const digest = crypto
        .createHash("sha256")
        .update(source)
        .digest("hex");
      // A draft about a source that has since changed would be stale the moment
      // it landed, so it is refused rather than written.
      if (candidate.sourceSha256 !== digest)
        return send(res, 409, {
          error: "The source changed; collect it again before keeping a draft",
        });
      await fs.writeFile(at, JSON.stringify(candidate, null, 2) + "\n");
      return send(res, 200, { path: path.relative(REPO, at), kept: true });
    }
    if (url.pathname === "/api/candidate") {
      const input = await readCandidate(req);
      if (analysing)
        return send(res, 409, {
          error: "Another operation is running; try again shortly",
        });
      analysing = true;
      try {
        return send(
          res,
          200,
          await candidateReport(input.candidate),
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
// Only a direct run serves: importing this module for `candidateReport` must
// not take the port.
if (process.argv[1] && import.meta.filename === path.resolve(process.argv[1])) {
  // A port already taken usually means a reader is up from an earlier run.
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
    console.log(`Claim report reader on ${url}`);
    // `--open` hands the page to the browser once the socket is actually
    // listening, so nothing races the server's start.
    if (process.argv.includes("--open")) {
      // An argument after `--open` names the page to open, so the reader being
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

export { candidateReport, analyse };
