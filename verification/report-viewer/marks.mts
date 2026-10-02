/* What the source view draws, decided without touching the DOM.
 *
 * Everything here is a pure function of a report, so it can be checked by the
 * report-viewer tests rather than by looking at a browser. Rendering — HTML,
 * events, selection — stays in viewer.js.
 */

/* ---------- positions ---------- */
import type { ShownFunction, ShownReport, Site } from "./model.mts";

/** What a mark is drawn against: the report's own text, and the producer's
 * diagnostics where it carried any. Both kinds of report the report viewer builds
 * satisfy it. */
export type MarkedReport = {
  source: string;
  file?: string;
  diagnostics?: string;
};

/** What an outcome is read from: the two verdicts a function carries, and —
 * where proof search stopped — what stopped it. */
export type Judged = Pick<ShownFunction, "status" | "failure" | "collection">;

/** What the source view was asked to draw. */
export interface MarkOptions {
  /** "key" keeps the claims worth reading; "all" keeps every one. */
  density?: string;
  /** Show claims the producer could not decode, which are otherwise noise. */
  unsupported?: boolean;
  producerErrors?: boolean;
}

/** One of the producer's own diagnostics, placed where it points. */
export interface ProducerMark {
  pos: [number, number];
  text: string;
  line: number;
}

/** One drawn mark: where it sits, what it says, and how it reads. */
export interface MarkItem {
  kind: string;
  line: number;
  /** Start column of the span the mark is about, in the monospace grid. */
  col: number;
  /** End column of that span; the bracket is drawn between the two. */
  end: number;
  label: string;
  /** A proof symbol where this claim is the located failure. */
  mark?: string;
  /** The obligation's role, where the record names one. */
  tag?: string;
  /** The mark's own key, for hover; and the site it stands for, where it does. */
  id: string;
  site: number | null;
  cls: string;
}

/** Marks packed onto as few rows as fit, so nesting is visible at a glance. */
export interface MarkRow {
  items: MarkItem[];
  free: number;
}

export interface SourceMarks {
  entries: MarkItem[];
  items: MarkItem[];
}


import obligationReader from "../tools/diagnostic-view.mts";

const lineStarts = (src: string) => {
  const a = [0];
  for (let i = 0; i < src.length; i++) if (src[i] === "\n") a.push(i + 1);
  return a;
};

function lineAt(starts: number[], pos: number) {
  let lo = 0,
    hi = starts.length;
  while (lo + 1 < hi) {
    const mid = (lo + hi) >> 1;
    if (starts[mid] <= pos) lo = mid;
    else hi = mid;
  }
  return lo;
}

const lineEndAt = (source: string, starts: number[], line: number) =>
  line + 1 < starts.length ? starts[line + 1] - 1 : source.length;

// Claim spans start at the declaration, but a comment written directly above a
// function belongs to it for whoever is reading. Take that block, stopping at a
// blank line or at anything that is not a comment, so a neighbour's trailing
// comment is never attributed here.
const COMMENT_LINE = /^\s*(\/\/|\/\*|\*)/;
function commentStartLine(source: string, starts: number[], from: number, floor: number) {
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
  "unavailable-type-claim",
  "source-limitation",
]);

const PROOF_LABEL: Record<string, string> = {
  verified: "verified",
  "not-established": "proof search failed",
  unsupported: "unsupported source",
  "not-run": "not run",
};
const proofLabel = (status: string) => PROOF_LABEL[status] || status;

/** Whether checking stopped for want of an input rather than at a judgement. */
const incompleteInput = (failureKind: string | undefined) =>
  failureKind !== undefined && INCOMPLETE_INPUT.has(failureKind);
const proofSymbol = (failureKind: string | undefined) =>
  incompleteInput(failureKind) ? "?" : "✗";

// A mark says which obligation stopped there when the record names a specific
// one. Without that, it stays silent rather than implying the claim is at fault.
const ROLE_TAG: Record<string, string> = {
  "unavailable-type-claim": "type unavailable",
  "parameter-claim": "parameter claim",
  "heap-observation": "current contents",
  "return-contract": "return contract",
  "binding-annotation": "binding annotation",
  "closure-entry": "closure entry",
  "closure-result": "closure result",
  "method-receiver": "method receiver",
};
const roleTag = (role: string) => ROLE_TAG[role] || "";

function proofMark(f: Judged): [string, string] {
  if (f.status === "verified") return ["✓", "a certificate was checked"];
  if (f.status === "unsupported")
    return [
      "?",
      "this source is outside the fragment, so nothing was checked",
    ];
  if (f.failure?.kind === "unavailable-type-claim")
    return [
      "?",
      "a type this needed was never decoded by the producer, so no obligation was reached",
    ];
  if (f.status === "not-established")
    return incompleteInput(f.failure?.kind)
      ? [
          "?",
          "checking could not proceed: a claim it needed is missing, or the source is outside the fragment",
        ]
      : ["✗", "proof search failed; that is not a disproof of the claim"];
  return ["·", "no verifier was available when this ran"];
}

// Grouping for the tally: what actually happened, which is the proof symbol. A
// function whose required type was never exported did not fail a proof search,
// and saying so in a count would be as wrong as saying it in a panel.
const OUTCOME_GROUP: Record<string, string> = {
  "✓": "verified",
  "✗": "proof search failed",
  "?": "could not be checked",
  "·": "not run",
};
const outcomeLabel = (symbol: string) => OUTCOME_GROUP[symbol] || symbol;
const outcomeGroup = (f: Judged) => {
  const [symbol] = proofMark(f);
  return { key: symbol, label: OUTCOME_GROUP[symbol] || proofLabel(f.status) };
};

const PRODUCER_MARK: Record<string, string[]> = {
  complete: ["✓", "Producer accepted this function"],
  aborted: ["✗", "Producer rejected this function"],
};

// Both outcomes, and whether they disagree. The producer's verdict reads only
// the source, so it holds for as long as the source does; proof search reads the claims,
// so an edit can change it. Where proof search reached no verdict there is no
// disagreement to report.
function outcome(
  f: Judged,
  collection: { verified: boolean } | null | undefined,
) {
  const producer = PRODUCER_MARK[f.collection ?? ""] || [
    "·",
    "no producer outcome recorded",
  ];
  const proof = proofMark(f);
  const concluded = !incompleteInput(f.failure?.kind);
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
        ? collection?.verified === true
          ? "fresh"
          : "recorded"
        : null,
    // The producer accepted it and proof search failed outright: worth an eye.
    attention:
      f.status === "not-established" && f.collection === "complete" && concluded,
  };
}

/* ---------- the producer's own diagnostics ---------- */
// A producer's diagnostics name the source with 1-based columns and an
// exclusive end.
// These are its diagnostics shown where they point: not claims, not results.
function producerMarks(rep: MarkedReport): ProducerMark[] {
  const marks: ProducerMark[] = [];
  if (!rep.diagnostics) return marks;
  const starts = lineStarts(rep.source);
  const re = /^File "([^"]+)", line (\d+), character (\d+)-(\d+):\r?\n([^\n]*)/gm;
  let m;
  while ((m = re.exec(rep.diagnostics))) {
    const [, file, line, from, to, text] = m;
    // Every group of the pattern above participates in a match, so a match
    // that reached here has them all.
    if (file === undefined || text === undefined) continue;
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
const isNoise = (b: { unavailable: boolean; type: string }) =>
  b.unavailable || b.type === "unsupported" || b.type === "(unavailable)";

// Gaps read better as a short phrase than as the generator's sentence.
const GAP_LABEL: Record<string, string> = {
  "statement-not-visited": "not visited by producer",
  "expression-without-type": "no type produced",
  "claims-unavailable": "no claims for this function",
  "claim-edit": "claim edit",
};
const gapLabel = (g: { reason: string; detail: string }) =>
  GAP_LABEL[g.reason] || g.detail;

function shortType(type: string) {
  // Surface syntax reads as a type; a raw producer encoding does not, and only
  // appears when this report viewer cannot name it.
  if (/^\{\s*"/.test(type)) return "structured type — inspect";
  return type.length > 64 ? type.slice(0, 61) + "…" : type;
}

// One mark per site or producer diagnostic in this function, positioned by
// line and column. Environments are drawn above their line and the rest below.
// The environment an expression obligation is checked against. Where the record
// names it, that is the answer; otherwise it is the innermost one containing the
// expression. Both are facts about the report, not a claim about what is wrong.
function companionEntry(f: ShownFunction) {
  const sites: Site[] = f.sites || [];
  const failing = f.failure?.at !== null && f.failure?.at !== undefined ? sites[f.failure.at] : null;
  if (!failing || failing.kind !== "expression") return -1;
  const obligation = f.obligation;
  const named =
    obligation && "source" in obligation
      ? obligation.source.sourceMap?.environmentStart
      : undefined;
  if (named !== null && named !== undefined) {
    const at = sites.findIndex((s) => s.kind === "environment" && s.pos[0] === named);
    if (at >= 0) return at;
  }
  let best = -1;
  sites.forEach((s, i) => {
    if (s.kind !== "environment" || s.pos[0] > failing.pos[0] || s.pos[1] < failing.pos[1]) return;
    if (best < 0 || s.pos[1] - s.pos[0] < sites[best].pos[1] - sites[best].pos[0]) best = i;
  });
  return best;
}

function sourceMarks(
  rep: MarkedReport,
  f: ShownFunction,
  options?: MarkOptions,
): SourceMarks {
  const { density = "key", unsupported = false, producerErrors = true } = options || {};
  const source = rep.source;
  const starts = lineStarts(source);
  const at = (p: number) => lineAt(starts, p);
  const sites: Site[] = f.sites || [];
  const failure = f.status === "not-established" ? f.failure : null;
  // A recovery-quality snapshot says so once, on the function; only a claim that
  // stands out from its snapshot needs the label repeated.
  const recMark = f.quality === "recovery" ? "" : "  (recovery)";
  const items: MarkItem[] = [];
  const entries: MarkItem[] = [];
  // Both sides of a failed obligation stay on screen. Compact hides an
  // environment where nothing changed, which is often the very one the marked
  // claim is checked against.
  const companion = failure ? companionEntry(f) : -1;
  // A mark's bracket stops at the end of its first line; the span may go on.
  const columns = (pos: readonly [number, number]) => {
    const line = at(pos[0]);
    const multiline = at(pos[1] - 1) !== line;
    return {
      line,
      col: pos[0] - starts[line],
      end: (multiline ? lineEndAt(source, starts, line) : pos[1]) - starts[line],
      multiline,
    };
  };

  sites.forEach((s, i) => {
    const failed = !!failure && failure.at === i;
    // A site proof search stopped at reads the same, with the proof outcome
    // added in the symbols the function pill uses.
    const mark = failed ? proofSymbol(failure?.kind) : "";
    const tag = failed ? roleTag(failure?.role || failure?.kind || "") : "";
    const flagged = failed ? " failed" : "";
    if (s.kind === "expression") {
      if (density === "key" && !failed) {
        // Compact keeps the outermost claim of a nest, and drops a literal that
        // only restates its own text.
        const nested = sites.some(
          (o) =>
            o.kind === "expression" &&
            o !== s &&
            o.pos[0] <= s.pos[0] &&
            o.pos[1] >= s.pos[1] &&
            (o.pos[0] < s.pos[0] || o.pos[1] > s.pos[1]),
        );
        if (nested) return;
        if (source.slice(s.pos[0], s.pos[1]).trim() === s.type.trim()) return;
      }
      const c = columns(s.pos);
      items.push({
        kind: "expr",
        id: "s" + i,
        site: i,
        line: c.line,
        col: c.col,
        end: c.end,
        label:
          shortType(s.type) + (c.multiline ? " ↳ multiline" : "") + (s.recovery ? recMark : ""),
        mark,
        tag,
        cls: "expr" + (s.recovery ? " rec" : "") + flagged,
      });
    } else if (s.kind === "result") {
      // What the function must establish, drawn at its annotation and read as
      // itself: every return is checked against it.
      const c = columns(s.pos);
      items.push({
        kind: "result",
        id: "s" + i,
        site: i,
        line: c.line,
        col: c.col,
        end: c.end,
        label: "returns " + shortType(s.type),
        mark,
        tag,
        cls: "result" + flagged,
      });
    } else if (s.kind === "unclaimed") {
      // A place with nothing claimed is always drawn where the report says why.
      // One the lowering merely attaches to is drawn in Every claim, and in
      // Compact only where verification is blocked, which is when an absent
      // claim is the thing to act on.
      if (s.claims && !s.detail && density !== "all" && f.status !== "not-established") return;
      const c = columns(s.pos);
      items.push({
        kind: s.claims ? "missing" : "gap",
        id: "s" + i,
        site: i,
        line: c.line,
        col: c.col,
        end: c.end,
        label: s.claims
          ? "no " + s.claims + " claim" + (s.detail ? " · " + gapLabel(s) : "")
          : gapLabel(s) + (failed && failure?.binding ? " · " + failure.binding : ""),
        mark,
        tag: s.claims ? "" : tag,
        cls: "gap" + (s.claims ? " missing" : "") + flagged,
      });
    } else {
      const involved = failed || i === companion;
      // An undecoded claim is normally noise. Where checking stopped at this
      // statement it is the finding, so it shows whatever the toggle says.
      const shown = s.bindings.filter((b) => unsupported || failed || !isNoise(b));
      // An environment the marked claim is checked against shows what it
      // claims, not only what changed there: nothing changing is exactly why
      // it can be the side that has to.
      const list =
        density === "key" && !involved ? shown.filter((b) => s.changed.has(b.name)) : shown;
      if (!list.length && !involved) return;
      const line = at(s.pos[0]);
      const col = s.pos[0] - starts[line];
      entries.push({
        kind: "entry",
        id: "s" + i,
        site: i,
        line,
        col,
        end: col,
        label:
          list.map((b) => b.name + ": " + shortType(b.type)).join(",  ") +
          (s.recovery ? recMark : ""),
        mark,
        tag,
        cls: "entry" + (s.recovery ? " rec" : "") + flagged,
      });
    }
  });

  // A failure whose place carries no site. Always drawn: it is the only thing
  // on screen saying where the function failed, and there is nothing else at
  // that position to click.
  if (failure && failure.at === null && failure.pos) {
    const c = columns(failure.pos);
    const title =
      (failure.role && obligationReader.roleView(failure.role).title) || "Obligation here";
    items.push({
      kind: "failure",
      id: "u",
      site: null,
      line: c.line,
      col: c.col,
      end: c.end,
      label: title.toLowerCase() + " · nothing claimed here",
      mark: proofSymbol(failure.kind),
      cls: "gap failed",
    });
  }

  if (producerErrors)
    producerMarks(rep).forEach((mark, i) => {
      if (mark.pos[0] < f.pos[0] || mark.pos[1] > f.pos[1]) return;
      const line = at(mark.pos[0]);
      const col = mark.pos[0] - starts[line];
      items.push({
        kind: "error",
        id: "p" + i,
        site: null,
        line,
        col,
        end: Math.max(mark.pos[1] - starts[line], col + 1),
        label: mark.text.length > 72 ? mark.text.slice(0, 69) + "…" : mark.text,
        cls: "err",
      });
    });

  return { entries, items };
}


/* ---------- laying marks out ---------- */
function bracket(w: number) {
  if (w <= 1) return "╵";
  return "╰" + "─".repeat(Math.max(0, w - 2)) + "╯";
}

// Marks are packed onto as few rows as fit, so nesting is visible at a glance.
// Width counts the bracket, the label and any proof symbol: these sit in a
// monospace grid, and a row that miscounts would overlap the next mark.
/** What packing needs of a mark: where it sits, and how wide it reads. */
type Packable = Pick<MarkItem, "col" | "end" | "label" | "mark" | "tag">;
const markWidth = (it: Packable) =>
  Math.max(1, it.end - it.col) +
  1 +
  it.label.length +
  (it.mark ? it.mark.length + 1 : 0) +
  (it.tag ? it.tag.length + 1 : 0);

function packRows<T extends Packable>(items: T[]): { items: T[]; free: number }[] {
  const rows: { items: T[]; free: number }[] = [];
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

function groupLines(items: MarkItem[]): Map<number, MarkItem[]> {
  const grouped = new Map<number, MarkItem[]>();
  for (const item of items) {
    const line = grouped.get(item.line) ?? [];
    line.push(item);
    grouped.set(item.line, line);
  }
  return grouped;
}

export {
    lineStarts,
    lineAt,
    commentStartLine,
    proofLabel,
    proofSymbol,
    roleTag,
    proofMark,
    outcomeGroup,
    outcomeLabel,
    outcome,
    producerMarks,
    isNoise,
    gapLabel,
    shortType,
    sourceMarks,
    companionEntry,
    bracket,
    markWidth,
    packRows,
    groupLines,
};