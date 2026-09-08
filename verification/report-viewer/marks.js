"use strict";
/* What the source view draws, decided without touching the DOM.
 *
 * Everything here is a pure function of a report, so it can be checked by the
 * report-viewer tests rather than by looking at a browser. Rendering — HTML,
 * events, selection — stays in viewer.js.
 */

/* ---------- positions ---------- */
const lineStarts = (src) => {
  const a = [0];
  for (let i = 0; i < src.length; i++) if (src[i] === "\n") a.push(i + 1);
  return a;
};

function lineAt(starts, pos) {
  let lo = 0,
    hi = starts.length;
  while (lo + 1 < hi) {
    const mid = (lo + hi) >> 1;
    if (starts[mid] <= pos) lo = mid;
    else hi = mid;
  }
  return lo;
}

const lineEndAt = (source, starts, line) =>
  line + 1 < starts.length ? starts[line + 1] - 1 : source.length;

// Claim spans start at the declaration, but a comment written directly above a
// function belongs to it for whoever is reading. Take that block, stopping at a
// blank line or at anything that is not a comment, so a neighbour's trailing
// comment is never attributed here.
const COMMENT_LINE = /^\s*(\/\/|\/\*|\*)/;
function commentStartLine(source, starts, from, floor) {
  let line = lineAt(starts, from);
  while (line > 0 && starts[line - 1] >= floor) {
    const text = source.slice(starts[line - 1], lineEndAt(source, starts, line - 1));
    if (!text.trim() || !COMMENT_LINE.test(text)) break;
    line--;
  }
  return line;
}

/* ---------- outcomes ---------- */
// ✓ proved, ✗ searched and failed, ? could not properly try, · nothing ran.
// "?" covers a claim the extractor needed and did not find — typically because
// the producer stopped before annotating everywhere — and source outside the
// fragment. "✗" means no proof was found, never that the claim is false.
const INCOMPLETE_INPUT = new Set([
  "missing-expression-claim",
  "missing-environment-claim",
  "source-limitation",
]);

const PROOF_LABEL = {
  verified: "verified",
  "not-established": "proof search failed",
  unsupported: "unsupported source",
  "not-run": "not run",
  stale: "stale after an edit",
};
const proofLabel = (status) => PROOF_LABEL[status] || status;

const proofSymbol = (failureKind) =>
  INCOMPLETE_INPUT.has(failureKind) ? "?" : "✗";

// A mark says which obligation stopped there when the record names a specific
// one. Without that, it stays silent rather than implying the claim is at fault.
const ROLE_TAG = {
  "return-contract": "return contract",
  "binding-annotation": "binding annotation",
  "closure-entry": "closure entry",
  "closure-result": "closure result",
};
const roleTag = (role) => ROLE_TAG[role] || "";

function proofMark(f) {
  if (f.status === "verified") return ["✓", "a certificate was checked"];
  if (f.status === "unsupported")
    return [
      "?",
      "the source fragment gate rejected this file, so nothing was checked",
    ];
  if (f.status === "not-established")
    return INCOMPLETE_INPUT.has(f.result?.location?.kind)
      ? [
          "?",
          "checking could not proceed: a claim it needed is missing, or the source is outside the fragment",
        ]
      : ["✗", "proof search failed; that is not a disproof of the claim"];
  if (f.status === "stale")
    return ["·", "stale: the candidate changed after this result"];
  return ["·", "no verifier was available when this ran"];
}

const PRODUCER_MARK = {
  complete: ["✓", "SKJS finished checking this function"],
  aborted: ["✗", "SKJS stopped inside this function"],
};

// Both outcomes, and whether they disagree. SKJS reads only the source, so its
// outcome holds for as long as the source does; proof search reads the claims,
// so an edit can change it. Where proof search reached no verdict there is no
// disagreement to report.
function outcome(f, rep) {
  const producer = PRODUCER_MARK[f.collection] || [
    "·",
    "no producer outcome recorded",
  ];
  const proof = proofMark(f);
  const concluded = !INCOMPLETE_INPUT.has(f.result?.location?.kind);
  const disagrees =
    concluded &&
    ((f.collection === "complete" && f.status === "not-established") ||
      (f.collection === "aborted" && f.status === "verified"));
  return {
    producer,
    proof,
    disagrees,
    // A verified function is stamped; the stamp is only solid when the consumer
    // ran for this report rather than the status having been read from a file.
    stamp:
      f.status === "verified"
        ? rep.collection?.verified === true
          ? "fresh"
          : "recorded"
        : null,
    // SKJS accepted it and proof search failed outright: worth an eye.
    attention:
      f.status === "not-established" && f.collection === "complete" && concluded,
  };
}

/* ---------- the producer's own diagnostics ---------- */
// SKJS reports against the source with 1-based columns and an exclusive end.
// These are its diagnostics shown where they point: not claims, not results.
function producerMarks(rep) {
  const marks = [];
  if (!rep.diagnostics) return marks;
  const starts = lineStarts(rep.source);
  const re = /^File "([^"]+)", line (\d+), character (\d+)-(\d+):\r?\n([^\n]*)/gm;
  let m;
  while ((m = re.exec(rep.diagnostics))) {
    const [, file, line, from, to, text] = m;
    if (rep.file && !file.endsWith(rep.file)) continue;
    const ln = Number(line) - 1;
    if (!(ln >= 0 && ln < starts.length)) continue;
    const end = lineEndAt(rep.source, starts, ln);
    const start = Math.min(starts[ln] + Number(from) - 1, end);
    marks.push({
      pos: [start, Math.min(Math.max(starts[ln] + Number(to) - 1, start + 1), end)],
      text: text.trim(),
      line: ln,
    });
  }
  return marks;
}

/* ---------- what the source view shows ---------- */
const isNoise = (b) =>
  b.unavailable || b.type === "unsupported" || b.type === "(unavailable)";

// Gaps read better as a short phrase than as the generator's sentence.
const GAP_LABEL = {
  "statement-not-visited": "not visited by producer",
  "expression-without-type": "no type produced",
  "claims-unavailable": "no claims for this function",
  "claim-edit": "claim edit",
};
const gapLabel = (g) => GAP_LABEL[g.reason] || g.detail;

function shortType(type) {
  if (type.startsWith("{")) return "structured type — inspect";
  return type.length > 64 ? type.slice(0, 61) + "…" : type;
}

// One mark per claim, gap or producer diagnostic in this function, positioned
// by line and column. `entries` are drawn above their line and `items` below.
function sourceMarks(rep, f, options) {
  const { density = "key", unsupported = false, producerErrors = true } = options || {};
  const source = rep.source;
  const starts = lineStarts(source);
  const at = (p) => lineAt(starts, p);
  const failedIn = (x) => f.status === "not-established" && Boolean(x.failure);
  // A recovery-quality snapshot says so once, on the function; only a claim that
  // stands out from its snapshot needs the label repeated.
  const recMark = f.quality === "recovery" ? "" : "  (recovery)";
  const items = [];
  const entries = [];

  f.exprs.forEach((e, i) => {
    if (!e.pos) return;
    const failed = failedIn(e);
    if (density === "key" && !failed) {
      const nested = f.exprs.some(
        (other) =>
          other !== e &&
          other.pos &&
          other.pos[0] <= e.pos[0] &&
          other.pos[1] >= e.pos[1] &&
          (other.pos[0] < e.pos[0] || other.pos[1] > e.pos[1]),
      );
      if (nested) return;
      if (source.slice(e.pos[0], e.pos[1]).trim() === e.type.trim()) return;
    }
    const line = at(e.pos[0]);
    const multiline = at(e.pos[1] - 1) !== line;
    items.push({
      kind: "expr",
      line,
      col: e.pos[0] - starts[line],
      end: multiline
        ? lineEndAt(source, starts, line) - starts[line]
        : e.pos[1] - starts[line],
      label:
        shortType(e.type) +
        (multiline ? " ↳ multiline" : "") +
        (e.recovery ? recMark : ""),
      // A claim proof search stopped at is still a claim: it reads the same,
      // with the proof outcome added in the symbols the function pill uses.
      mark: failed ? proofSymbol(e.failureKind) : "",
      tag: failed ? roleTag(e.failureRole) : "",
      id: "e" + i,
      cls: "expr" + (e.recovery ? " rec" : "") + (failed ? " failed" : ""),
    });
  });

  f.gaps.forEach((g, i) => {
    // Always shown: an absent claim is the finding.
    const line = at(g.pos[0]);
    const failed = failedIn(g);
    items.push({
      kind: "gap",
      line,
      col: g.pos[0] - starts[line],
      end:
        (at(g.pos[1] - 1) === line ? g.pos[1] : lineEndAt(source, starts, line)) -
        starts[line],
      label:
        gapLabel(g) +
        (failed && g.failureBinding ? " · " + g.failureBinding : ""),
      mark: failed ? proofSymbol(g.failureKind) : "",
      id: "g" + i,
      cls: "gap" + (failed ? " failed" : ""),
    });
  });

  if (producerErrors)
    producerMarks(rep).forEach((mark, i) => {
      if (mark.pos[0] < (f.start || 0) || mark.pos[1] > (f.end ?? source.length))
        return;
      const line = at(mark.pos[0]);
      const col = mark.pos[0] - starts[line];
      items.push({
        kind: "error",
        line,
        col,
        end: Math.max(mark.pos[1] - starts[line], col + 1),
        label: mark.text.length > 72 ? mark.text.slice(0, 69) + "…" : mark.text,
        id: "p" + i,
        cls: "err",
      });
    });

  f.entries.forEach((e, i) => {
    if (!e.pos) return;
    const shown = e.bindings.filter((b) => unsupported || !isNoise(b));
    const list = density === "key" ? shown.filter((b) => e.changed.has(b.name)) : shown;
    const failed = failedIn(e);
    if (!list.length && !failed) return;
    const line = at(e.pos[0]),
      col = e.pos[0] - starts[line];
    entries.push({
      kind: "entry",
      line,
      col,
      end: col,
      label:
        list.map((b) => b.name + ": " + shortType(b.type)).join(",  ") +
        (e.recovery ? recMark : ""),
      mark: failed ? proofSymbol(e.failureKind) : "",
      tag: failed ? roleTag(e.failureRole) : "",
      id: "n" + i,
      cls: "entry" + (e.recovery ? " rec" : "") + (failed ? " failed" : ""),
    });
  });

  return { entries, items };
}

// The first failure the report located, in the order the source view marks them.
function firstFailure(f) {
  for (const [prefix, list] of [
    ["e", f.exprs],
    ["n", f.entries],
    ["g", f.gaps],
  ]) {
    const i = (list || []).findIndex((x) => x.failure);
    if (i >= 0) return { id: prefix + i, item: list[i], kind: list[i].failureKind };
  }
  return null;
}

/* ---------- laying marks out ---------- */
function bracket(w) {
  if (w <= 1) return "╵";
  return "╰" + "─".repeat(Math.max(0, w - 2)) + "╯";
}

// Marks are packed onto as few rows as fit, so nesting is visible at a glance.
// Width counts the bracket, the label and any proof symbol: these sit in a
// monospace grid, and a row that miscounts would overlap the next mark.
const markWidth = (it) =>
  Math.max(1, it.end - it.col) +
  1 +
  it.label.length +
  (it.mark ? it.mark.length + 1 : 0) +
  (it.tag ? it.tag.length + 1 : 0);

function packRows(items) {
  const rows = [];
  items.sort((a, b) => a.col - b.col || a.end - b.end);
  for (const it of items) {
    let row = rows.find((r) => r.free <= it.col);
    if (!row) {
      row = { items: [], free: 0 };
      rows.push(row);
    }
    row.items.push(it);
    row.free = it.col + markWidth(it) + 1;
  }
  return rows;
}

function groupLines(items) {
  const grouped = new Map();
  for (const item of items) {
    if (!grouped.has(item.line)) grouped.set(item.line, []);
    grouped.get(item.line).push(item);
  }
  return grouped;
}

if (typeof module !== "undefined")
  module.exports = {
    lineStarts,
    lineAt,
    commentStartLine,
    proofLabel,
    proofSymbol,
    roleTag,
    proofMark,
    outcome,
    producerMarks,
    isNoise,
    gapLabel,
    shortType,
    sourceMarks,
    firstFailure,
    bracket,
    markWidth,
    packRows,
    groupLines,
  };
