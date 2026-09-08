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
const examples = require("./examples.js");

async function repositoryPath(relative) {
  const resolved = await fs.realpath(path.resolve(REPO, relative));
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

async function analyse(relative, verify) {
  const sourcePath = await repositoryPath(relative);
  const source = await fs.readFile(sourcePath, "utf8");
  const tmp = await fs.mkdtemp(path.join(os.tmpdir(), "claim-report-"));
  const options = { cwd: REPO, timeout: 120000, maxBuffer: 32 * 1024 * 1024 };
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
    if (verify) {
      if (!(await hasVerifier()))
        throw new Error(
          "Verification requested, but the verifier is unavailable",
        );
      args.push("--verify", VERIFIER);
    }
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

async function candidateReport(candidate, verify) {
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
    return { source, ...JSON.parse(result.stdout), candidate };
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
    if (url.pathname === "/api/files")
      return send(res, 200, {
        files: examples.supported,
        groups: examples.groups,
      });
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
            url.searchParams.get("verify") === "1",
          ),
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
          await candidateReport(input.candidate, input.verify === true),
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
