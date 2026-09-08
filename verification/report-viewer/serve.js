#!/usr/bin/env node
"use strict";

const http = require("node:http");
const fs = require("node:fs/promises");
const path = require("node:path");
const os = require("node:os");
const { promisify } = require("node:util");
const execFile = promisify(require("node:child_process").execFile);

const REPO = path.resolve(
  process.env.SKJS_REPO || path.join(__dirname, "../.."),
);
const VERIFIER = "verification/lean/.lake/build/bin/verifier";
const PORT = Number(process.env.PORT || 8731);
const EXAMPLES = "./examples.js";
// Read the example groups per request: editing that list should show up on the
// next page load, not only after restarting this server.
function exampleGroups() {
  delete require.cache[require.resolve(EXAMPLES)];
  return require(EXAMPLES);
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
let listing = { at: 0, files: [] };
async function sources() {
  if (Date.now() - listing.at < 10000) return listing.files;
  const files = [];
  const walk = async (dir) => {
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
      else if (/\.(ts|tsx|mts|cts)$/.test(entry.name) && !entry.isSymbolicLink())
        files.push(path.relative(REPO, full));
    }
  };
  await walk(REPO);
  files.sort();
  listing = { at: Date.now(), files };
  return files;
}

async function repositoryPath(relative) {
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

// Verification is not an option the caller turns on: if a verifier is present it
// runs, so what is displayed is always checked against the claims on screen.
async function analyse(relative) {
  const sourcePath = await repositoryPath(relative);
  const source = await fs.readFile(sourcePath, "utf8");
  const tmp = await fs.mkdtemp(path.join(os.tmpdir(), "claim-report-"));
  const options = { cwd: REPO, timeout: 120000, maxBuffer: 32 * 1024 * 1024 };
  // Every request runs the producer: nothing here is cached or reused. The
  // reader shows when it ran, so a displayed report is never mistaken for an
  // older one.
  const startedAt = Date.now();
  try {
    let run;
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
    } catch (error) {
      // Normal rejection can still yield a partial collection. Operational errors cannot.
      if (
        error.killed ||
        typeof error.code !== "number" ||
        !error.stdout?.trim().startsWith("[")
      )
        throw error;
      run = error;
    }
    const claims = path.join(tmp, "claims.json");
    await fs.writeFile(claims, run.stdout);
    const args = [
      "verification/tools/annotate-source.js",
      relative,
      "--claims",
      claims,
      "--producer",
      "skjs",
      "--format",
      "skjs",
      "--stdout",
      "json",
    ];
    if (run.stderr.trim()) {
      const diagnostics = path.join(tmp, "diagnostics.txt");
      await fs.writeFile(diagnostics, run.stderr);
      args.push("--diagnostics", diagnostics);
    }
    const verify = await hasVerifier();
    if (verify) args.push("--verify", VERIFIER);
    const result = await execFile(process.execPath, args, options);
    const bundle = JSON.parse(result.stdout);
    if (source !== (await fs.readFile(sourcePath, "utf8")))
      throw new Error("Source changed during collection; run again");
    const digest = require("node:crypto")
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
        format: "skjs",
        file: relative,
        sourceSha256: digest,
        claims: JSON.parse(run.stdout).filter((f) => f.file === relative),
      },
    };
  } finally {
    await fs.rm(tmp, { recursive: true, force: true });
  }
}

// `verify` exists for callers that want attachment validation on its own; the
// HTTP route never passes it, so nothing a browser asks for skips checking.
async function candidateReport(candidate, verify = true) {
  const startedAt = Date.now();
  if (
    !candidate ||
    !["skjs", "source-claims"].includes(candidate.format) ||
    typeof candidate.file !== "string"
  )
    throw new Error("Unsupported candidate format");
  const sourcePath = await repositoryPath(candidate.file);
  const source = await fs.readFile(sourcePath, "utf8");
  const digest = require("node:crypto")
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
      "verification/tools/annotate-source.js",
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

async function readCandidate(req) {
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

const assets = new Map([
  ["/", ["claim-report-viewer.html", "text/html"]],
  ["/viewer.js", ["viewer.js", "text/javascript"]],
  ["/model.js", ["model.js", "text/javascript"]],
  ["/types.js", ["types.js", "text/javascript"]],
  ["/marks.js", ["marks.js", "text/javascript"]],
  ["/obligation.js", ["obligation.js", "text/javascript"]],
  ["/candidate.js", ["candidate.js", "text/javascript"]],
  ["/editor.js", ["editor.js", "text/javascript"]],
  ["/viewer.css", ["viewer.css", "text/css"]],
]);
const send = (res, status, data, type = "application/json") => {
  res.writeHead(status, {
    "content-type": type + "; charset=utf-8",
    "cache-control": "no-store",
  });
  res.end(type === "application/json" ? JSON.stringify(data) : data);
};

// Bound concurrency: expensive runs do not block file loading or health checks.
let analysing = false;
const server = http.createServer(async (req, res) => {
  const url = new URL(req.url, "http://localhost");
  try {
    if (url.pathname === "/api/health")
      return send(res, 200, { verifier: await hasVerifier() });
    if (url.pathname === "/api/files") {
      const examples = exampleGroups();
      return send(res, 200, {
        files: examples.supported,
        groups: examples.groups,
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
  } catch (error) {
    send(res, 500, {
      error: String(error.stderr || error.message).slice(0, 4000),
    });
  }
});
if (require.main === module)
  server.listen(PORT, "127.0.0.1", () =>
    console.log(`Claim report reader on http://localhost:${PORT}`),
  );

module.exports = { candidateReport };
