#!/usr/bin/env node
/*
 * The drafts kept beside the corpus sources.
 *
 * A draft is a claim set for one exact source: its `sourceSha256` must match,
 * and its spans describe that text. A committed one is therefore stale the
 * moment its source is touched, and a stale draft is silently ignored by the
 * reader — which is the right thing for the reader and the wrong thing for the
 * tree, because nothing would say so.
 *
 * So this checks every kept draft: that it is about a source that exists, that
 * it is about that source as it is now, and that the verifier still establishes
 * what it claims. A draft that stops verifying is a finding about the verifier
 * or about the claims, not a file to regenerate without reading.
 */
import assert from "node:assert/strict";
import fs from "node:fs";
import path from "node:path";
import { createHash } from "node:crypto";
import { candidateReport } from "../report-viewer/serve.mts";

const root = path.resolve(path.dirname(import.meta.filename), "../..");
process.chdir(root);

/** Every draft in the corpus, by the source it is about. */
function drafts(dir: string): string[] {
  const found: string[] = [];
  for (const entry of fs.readdirSync(dir, { withFileTypes: true })) {
    const at = path.join(dir, entry.name);
    if (entry.isDirectory()) found.push(...drafts(at));
    else if (entry.name.endsWith(".candidate.json")) found.push(at);
  }
  return found;
}

const kept = drafts("verification/tests").sort();
let passed = 0;

for (const at of kept) {
  const relative = path.relative(root, at);
  const draft = JSON.parse(fs.readFileSync(at, "utf8"));

  assert(
    ["skjs", "source-claims"].includes(draft.format),
    `${relative}: unsupported candidate format`,
  );
  assert(
    fs.existsSync(draft.file),
    `${relative} is about ${draft.file}, which does not exist`,
  );
  // The draft's own name says which source it belongs beside; its `file` says
  // which source it is about. Disagreement means one of the two moved.
  assert.equal(
    relative.replace(/\.candidate\.json$/, ".ts"),
    draft.file,
    `${relative} sits beside a different source than it names`,
  );

  const source = fs.readFileSync(draft.file, "utf8");
  const digest = createHash("sha256").update(source).digest("hex");
  assert.equal(
    draft.sourceSha256,
    digest,
    `${relative} is about ${draft.file} as it was before it changed; ` +
      `re-derive it against the source as it is, rather than editing the hash`,
  );

  const report = await candidateReport(draft, true);
  const results = report.manifest.results ?? [];
  assert(results.length, `${relative}: nothing was checked`);
  for (const result of results)
    assert.equal(
      result.status,
      "verified",
      `${relative}: ${result.function} is ${result.status} — ` +
        `a draft that stops verifying is a finding, not a file to regenerate`,
    );
  passed++;
  console.log(`  ${relative}: ${results.length} verified`);
}

console.log(`Kept drafts: ${passed} checked, 0 failed`);
