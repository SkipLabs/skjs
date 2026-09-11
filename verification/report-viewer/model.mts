// Surface type printing is shared with the report writer.
import type { Bundle, Producer } from "./types.ts";
import type { Span } from "../tools/source-claims.mts";

/** A claim as the reader shows it, after the model has decoded its type. */
export interface ShownClaim {
  pos: Span;
  /** Surface syntax, printed from the producer's encoding. */
  type: string;
  /** The producer's own encoding, or null where there was none. */
  encoding: unknown;
  /** That encoding as formatted JSON, for the inspector. */
  raw: string | null;
  recovery?: boolean;
  unavailable?: boolean;
  failure?: string;
  failureKind?: string;
  failureRole?: string;
}

export interface ShownBinding {
  name: string;
  type: string;
  encoding?: unknown;
  raw?: string | null;
}

export interface ShownEntry {
  pos: Span;
  bindings: ShownBinding[];
  /** Names whose type differs from the preceding entry's. */
  changed: Set<string>;
  recovery?: boolean;
  unsupported?: string[];
  failure?: string;
  failureKind?: string;
}

export interface ShownGap {
  pos: Span;
  detail: string;
  reason: string;
  failure?: string;
  failureKind?: string;
}

/** One function of the report, with everything the view draws for it. */
export interface ShownFunction {
  id: string;
  name: string;
  namePos: Span;
  pos: Span;
  signature?: { params: { name: string; type: string }[]; retType: string };
  entries: ShownEntry[];
  exprs: ShownClaim[];
  gaps: ShownGap[];
  /** Sites a located failure names where nothing is claimed. */
  failureSites?: ShownClaim[];
  missingSites?: { kind: "expression" | "environment"; pos: Span }[];
  /** True for a source function the candidate says nothing about at all. */
  candidateMissing?: boolean;
  /** Its parameter names, in source order, for the contract it needs. */
  parameters?: string[];
  /** What the report says about it, where there is no result to report. */
  detail?: string;
  /** The verifier's verdict over this function's claims. */
  status: string;
  /** The producer's own collection outcome. */
  collection?: { completion: string; quality: string; mode: string };
  quality?: string;
  failure?: string;
  obligation?: unknown;
}

export interface Report {
  source: string;
  producer: Producer | string;
  functions: ShownFunction[];
  diagnostics?: string;
  missingFunctions?: { name: string; namePos: Span }[];
}


import SURFACE from "../tools/claim-types.mts";
const printSurface = (type: any) => SURFACE.printType(type);

/* ---------- reading the annotated format ---------- */
const RE_COMMENT = /\/\*\s*@verify-report([\s\S]*?)\*\//g;

function unescapeText(s: any) {
  try {
    return JSON.parse('"' + s.replace(/\n/g, " ") + '"');
  } catch (e) {
    return s;
  }
}

// split "a: T, b: U" on top-level commas (types may be raw JSON)
function splitTop(s: any, sep: any) {
  const out: any[] = [];
  let depth = 0,
    q = null,
    cur = "";
  for (const ch of s) {
    if (q) {
      cur += ch;
      if (ch === q && cur[cur.length - 2] !== "\\") q = null;
      continue;
    }
    if (ch === '"' || ch === "'") {
      q = ch;
      cur += ch;
      continue;
    }
    if (ch === "{" || ch === "[") depth++;
    if (ch === "}" || ch === "]") depth--;
    if (ch === sep && depth === 0) {
      out.push(cur);
      cur = "";
      continue;
    }
    cur += ch;
  }
  if (cur.trim()) out.push(cur);
  return out.map((x) => x.trim());
}

function renderType(text: string) {
  const value = (text || "").trim();
  // Display text is already produced by the report writer. Never reinterpret
  // unknown producer encodings as a different type.
  return { text: value, raw: value.startsWith("{") ? value : null };
}

function parseReport(annotated: any) {
  const rep: Record<string, any> = {
    producer: "unknown",
    file: "(unknown source)",
    meta: {} as Record<string, any>,
    functions: [] as any[],
    source: "",
  };
  let src = "",
    last = 0,
    cur = null;
  RE_COMMENT.lastIndex = 0;
  let m;
  while ((m = RE_COMMENT.exec(annotated))) {
    src += annotated.slice(last, m.index);
    last = m.index + m[0].length;
    if (annotated[last] === " ")
      last++; // generator's trailing space
    else if (annotated[last] === "\n") last++; // header block's newline
    const body = m[1];
    if (/^\s*\n/.test(body)) {
      // header block
      for (const line of body.split("\n")) {
        const kv = /^\s*\*?\s*([\w-]+)=(.*)$/.exec(line);
        if (kv) {
          const k = kv[1],
            v = unescapeText(kv[2].trim());
          if (k === "producer") rep.producer = v;
          else if (k === "source") rep.file = v;
          else if (k === "annotation-fields")
            rep.fields = v.split(","); // format declaration, not provenance
          else rep.meta[k] = v;
        }
      }
      continue;
    }
    const text = unescapeText(body.trim());
    const span = /@(\d+):(\d+)\s*$/.exec(text);
    const pos = span ? [+span[1], +span[2]] : null;
    let core = span ? text.slice(0, span.index).trim() : text;
    // The generator prefixes machine-readable fields; the prose after them is for
    // people. Reports written before those fields still parse by their prose.
    const fld: Record<string, any> = {};
    core = core
      .replace(/^(?:[a-z]+=[^;]*; )+/, (run: any) => {
        for (const kv of run.split("; ")) {
          const i = kv.indexOf("=");
          if (i > 0) fld[kv.slice(0, i)] = kv.slice(i + 1);
        }
        return "";
      })
      .trim();
    const kind =
      fld.kind ||
      (core.startsWith("function ")
        ? "function"
        : core.startsWith("entry ")
          ? "entry"
          : core.startsWith("expr ")
            ? "expression"
            : "gap");
    const unavailable = new Set(
      (fld.unsupported || "").split("+").filter(Boolean),
    );
    // claims produced after an error are marked; they are still only claims
    let recovery = false;
    if (core.endsWith("; recovery claim")) {
      recovery = true;
      core = core.slice(0, -16).trim();
    }
    if (kind === "function") {
      const parts = splitTop(core, ";");
      const f = {
        name: parts[0].replace(/^function\s+/, "").trim(),
        producer: "",
        signature: null,
        status: "not-run",
        detail: "",
        collection: "",
        quality: "",
        mode: "",
        entries: [],
        exprs: [],
        gaps: [] as any[],
      } as Record<string, any>;
      for (const p of parts.slice(1)) {
        if (p.startsWith("producer=")) f.producer = p.slice(9);
        else if (p.startsWith("claimed ")) f.signature = p.slice(8).trim();
        else if (p.startsWith("verification=")) f.status = p.slice(13).trim();
        else if (p.startsWith("collection=")) f.collection = p.slice(11).trim();
        else if (p.startsWith("quality=")) f.quality = p.slice(8).trim();
        else if (p.startsWith("mode=")) f.mode = p.slice(5).trim();
        else f.detail = (f.detail ? f.detail + "; " : "") + p;
      }
      f.id = fld.id || "";
      f.start = src.length;
      rep.functions.push(f);
      cur = f;
    } else if (kind === "entry") {
      const inner = core.replace(/^entry\s*\{/, "").replace(/\}\s*$/, "");
      const bindings = splitTop(inner, ",").map((b) => {
        const i = b.indexOf(":");
        const name = b.slice(0, i).trim(),
          ty = renderType(b.slice(i + 1));
        return {
          name,
          type: ty.text,
          raw: ty.raw,
          unavailable: unavailable.has(name) || ty.text === "unsupported",
        };
      });
      if (cur) cur.entries.push({ pos, bindings, recovery, id: fld.id || "" });
    } else if (kind === "expression") {
      const ty = renderType(core.replace(/^expr\s+/, ""));
      if (cur)
        cur.exprs.push({
          pos,
          type: ty.text,
          raw: ty.raw,
          recovery,
          id: fld.id || "",
        });
    } else if (pos && cur) {
      // a gap is a place the producer entered but did not claim, or an edit
      // against a baseline. Its reason is a slug; the prose is the long form.
      cur.gaps.push({
        pos,
        detail: core,
        reason: fld.reason || "",
        id: fld.id || "",
      });
    }
  }
  src += annotated.slice(last);
  rep.source = src;
  for (let i = 0; i < rep.functions.length; i++)
    rep.functions[i].end = rep.functions[i + 1]?.start ?? src.length;
  // mark, per entry, which bindings changed since the previous entry of that function
  for (const f of rep.functions) {
    let prev = new Map();
    for (const e of f.entries) {
      e.changed = new Set();
      for (const b of e.bindings)
        if (prev.get(b.name) !== b.type) e.changed.add(b.name);
      prev = new Map(e.bindings.map((b: any) => [b.name, b.type]));
    }
  }
  return rep;
}

// A function's contract, in the same syntax as its claims.
function signatureText(signature: any) {
  const part = (type: any) => {
    const printed = printSurface(type);
    return printed.printable ? printed.text : JSON.stringify(type);
  };
  const params = (signature.params || [])
    .map((p: any) => (p.name ? p.name + ": " : "") + part(p.type))
    .join(", ");
  return "(" + params + ") => " + part(signature.retType);
}

function fromBundle(bundle: any) {
  const { source, manifest: m } = bundle;
  if (
    typeof source !== "string" ||
    m?.version !== 1 ||
    !Array.isArray(m.functions)
  )
    throw new Error("Expected source text and a version 1 report manifest");
  const span = (pos: any) => {
    if (
      !Array.isArray(pos) ||
      pos.length !== 2 ||
      !pos.every(Number.isSafeInteger) ||
      pos[0] < 0 ||
      pos[0] >= pos[1] ||
      pos[1] > source.length
    )
      throw new Error("Invalid claim source span");
    return pos;
  };
  const missingSites = (f: any, pos: any) =>
    (f.missingSites || []).map((site: any) => {
      if (!["expression", "environment"].includes(site.kind))
        throw new Error("Invalid missing claim kind");
      span(site.pos);
      if (site.pos[0] < pos[0] || site.pos[1] > pos[1])
        throw new Error("Missing site outside function");
      return site;
    });
  const raw = (x: any) => (x === undefined ? null : JSON.stringify(x, null, 2));
  // Claims are shown in the syntax they were written in. The producer's display
  // string is the fallback: it is what a report carries when there is no
  // encoding to print, and the exact encoding stays available beside it.
  const display = (encoding: any, fallback: any) => {
    if (encoding === undefined || encoding === null) return fallback;
    const printed = printSurface(encoding);
    return printed.printable ? printed.text : fallback;
  };
  const gaps = [
    ...(m.gaps || []),
    ...(m.comparison?.changes || []).map((c: any, i: number) => ({
      id: `g${(m.gaps || []).length + i}`,
      pos: c.span,
      status: `claim edit: ${c.status} ${c.kind}`,
    })),
  ];
  const functions = m.functions.map((f: any) => {
    const pos = span(f.pos);
    const result = m.results?.find((r: any) => r.function === f.id);
    const recovery = f.collection?.quality === "recovery";
    return {
      ...f,
      missingSites: missingSites(f, pos),
      start: pos[0],
      end: pos[1],
      signature: f.signature ? signatureText(f.signature) : null,
      status: result?.status || "not-run",
      // The diagnostic is what a reader needs; the whole record stays available
      // for provenance, and neither is evidence.
      detail: result?.detail || "",
      result: result || null,
      // Explanatory metadata about an unsuccessful attempt, kept as recorded.
      obligation: result?.obligation || null,
      collection: f.collection?.completion || "",
      quality: f.collection?.quality || "",
      mode: f.collection?.mode || "",
      entries: f.entries.map((e: any) => ({
        ...e,
        pos: span(e.pos),
        recovery,
        changed: new Set(),
        bindings: e.bindings.map((b: any) => ({
          ...b,
          type: display(b.raw, b.type),
          encoding: b.raw ?? null,
          raw: raw(b.raw),
          unavailable: b.raw?.unsupported === true,
        })),
      })),
      exprs: f.expressions.map((e: any) => ({
        ...e,
        pos: span(e.pos),
        recovery,
        type: display(e.raw, e.type),
        encoding: e.raw ?? null,
        raw: raw(e.raw),
      })),
      gaps: gaps
        .filter((g) => g.pos[0] >= pos[0] && g.pos[1] <= pos[1])
        .map((g) => ({
          ...g,
          pos: span(g.pos),
          detail: g.status,
          reason:
            g.status === "statement not visited" ? "statement-not-visited" : "",
        })),
    };
  });
  for (const f of functions) {
    f.entries.sort((a: any, b: any) => a.pos[0] - b.pos[0]);
    let previous = new Map();
    for (const e of f.entries) {
      e.changed = new Set(
        e.bindings
          .filter((b: any) => previous.get(b.name) !== b.type)
          .map((b: any) => b.name),
      );
      previous = new Map(e.bindings.map((b: any) => [b.name, b.type]));
    }
  }
  for (const f of functions) {
    const result = m.results?.find((r: any) => r.function === f.id);
    const location = result?.location;
    if (f.status !== "not-established" || !location) continue;
    // Where a location does not land on a claim, the record's own environment
    // offset says which statement entry it belongs to.
    const entryStart = (result: any, location: any) =>
      result.obligation?.destination?.sourceMap?.environmentStart ??
      result.obligation?.source?.sourceMap?.environmentStart ??
      location.start ??
      (Array.isArray(location.pos) ? location.pos[0] : undefined);
    const samePos = (x: any) =>
      location.pos !== undefined &&
      JSON.stringify(x.pos) === JSON.stringify(location.pos);
    // A claim the verifier needed and did not find belongs on the gap that
    // already marks that place. Falling back to a claim at the same position
    // keeps older reports, where no gap was recorded, locatable.
    const failed =
      // A required type the producer never decoded: no obligation was reached,
      // so this attaches to the claim that is missing one, not to a judgement.
      location.kind === "unavailable-type-claim"
        ? location.start !== undefined
          ? f.entries.find((e: any) => e.pos[0] === location.start)
          : f.exprs.find(samePos)
        : location.kind === "missing-expression-claim"
        ? f.gaps.find(samePos) || f.exprs.find(samePos)
        : location.kind === "missing-environment-claim"
          ? f.gaps.find((g: any) => g.pos[0] === location.start) ||
            f.entries.find((e: any) => e.pos[0] === location.start)
          : location.kind === "environment-obligation"
            ? f.entries.find((e: any) => e.pos[0] === location.start)
            : // A parameter claim contradicting its annotation: the first entry
              // that names the parameter is where the reader sees the claim.
              location.kind === "parameter-claim"
              ? f.entries.find((e: any) =>
                  e.bindings.some((b: any) => b.name === location.binding),
                )
            : [
                  "expression-obligation",
                  "edge-obligation",
                  "source-limitation",
                ].includes(location.kind)
              ? // A span names an expression claim when there is one. An edge
                // into a statement checkpoint has none: its destination is the
                // entry, which the record names.
                f.exprs.find(samePos) ||
                f.entries.find((e: any) => e.pos[0] === entryStart(result, location))
              : null;
    if (failed) {
      failed.failure =
        result.detail || "Proof search did not establish this obligation.";
      failed.failureKind = location.kind;
      failed.failureBinding = location.binding || "";
      failed.failureStage = result.stage || "";
      // Which obligation stopped here — a return contract at a return statement
      // is not the expression's own claim, even though they share a span.
      // For an edge, the role that describes where this attached is the
      // destination's; `source` describes the other end.
      const destination = result.obligation?.destination?.sourceMap;
      failed.failureRole =
        (destination &&
        destination.environmentStart === failed.pos?.[0]
          ? destination.role
          : "") ||
        result.obligation?.source?.sourceMap?.role ||
        result.obligation?.sourceMap?.role ||
        "";
    } else if (Array.isArray(location.pos)) {
      // A failure with a position but nothing claimed there. An obligation the
      // extractor states about a place the producer never wrote a claim for -
      // a body that completes, say - is still real and still locatable, so it
      // gets a mark of its own instead of only a sentence at the top of the
      // function saying no location is available.
      f.failureSites = (f.failureSites || []).concat([
        {
          pos: span(location.pos),
          failure:
            result.detail || "Proof search did not establish this obligation.",
          failureKind: location.kind,
          failureRole:
            result.obligation?.source?.sourceMap?.role ||
            result.obligation?.sourceMap?.role ||
            "",
        },
      ]);
    }
  }

  for (const f of m.missingFunctions || []) {
    const pos = span(f.pos);
    span(f.namePos);
    if (
      f.namePos[0] < pos[0] ||
      f.namePos[1] > pos[1] ||
      functions.some((existing: any) => existing.namePos?.[0] === f.namePos[0])
    )
      throw new Error("Invalid missing function identity");
    if (
      !Array.isArray(f.parameters) ||
      f.parameters.some((p: any) => typeof p !== "string")
    )
      throw new Error("Invalid missing function parameters");
    functions.push({
      ...f,
      id: `missing-${f.namePos[0]}`,
      start: pos[0],
      end: pos[1],
      candidateMissing: true,
      missingSites: missingSites(f, pos),
      status: "not-established",
      detail:
        "No function candidate supplied. Add its contract before adding point claims.",
      entries: [],
      exprs: [],
      gaps: gaps
        .filter((g) => g.pos[0] >= pos[0] && g.pos[1] <= pos[1])
        .map((g) => ({ ...g, detail: g.status })),
    });
  }
  functions.sort((a: any, b: any) => a.start - b.start);
  const unattached = gaps.filter(
    (g) => !functions.some((f: any) => g.pos[0] >= f.start && g.pos[1] <= f.end),
  );
  if (unattached.length)
    functions.push({
      name: "Other coverage gaps",
      start: 0,
      end: source.length,
      status: "not-established",
      entries: [],
      exprs: [],
      gaps: unattached.map((g) => ({
        ...g,
        pos: span(g.pos),
        detail: g.status,
      })),
    });
  return {
    source,
    functions,
    file: m.source.file,
    producer: m.producer,
    diagnostics:
      (bundle.originalDiagnostics && m.diagnostics
        ? "Original producer snapshot:\n"
        : "") + (m.diagnostics || ""),
    // What produced this report and when, as reported by the local runner. It
    // records that a command ran, not that anything was established.
    collection: bundle.collection || null,
    meta: {
      "source-sha256": m.source.sha256,
      ...Object.fromEntries(
        Object.entries(m).filter(([key]) => key.endsWith("Sha256")),
      ),
    },
    manifest: m,
  };
}
/* ---------- naming a claim across sessions ---------- */
// Marks are addressed inside the page by their position in a function's lists,
// which changes whenever claims change. The manifest id assigned by the report
// writer does not: it is what a link, or a person quoting an id, should name.
const MARK_LISTS = [
  ["e", "exprs"],
  ["n", "entries"],
  ["g", "gaps"],
];

function findMark(report: any, manifestId: any) {
  if (!manifestId) return null;
  for (let fn = 0; fn < report.functions.length; fn++) {
    const f = report.functions[fn];
    if (f.id === manifestId) return { fn, id: null, manifestId };
    for (const [prefix, list] of MARK_LISTS) {
      const i = (f[list] || []).findIndex((x: any) => x.id === manifestId);
      if (i >= 0) return { fn, id: prefix + i, manifestId };
    }
  }
  return null;
}

function markIdOf(report: any, fn: any, id: any) {
  const f = report.functions[fn];
  if (!f) return "";
  if (!id) return f.id || "";
  const entry = MARK_LISTS.find(([prefix]) => prefix === id[0]);
  return (entry && f[entry[1]]?.[+id.slice(1)]?.id) || "";
}

// Movement through the marks as drawn. It wraps, and an unknown current
// position starts at the end nearest the direction of travel, so the first key
// press always lands on something.
function nextMark(marks: any, current: any, step: any) {
  if (!marks.length) return null;
  const at = marks.indexOf(current);
  if (at < 0) return step > 0 ? marks[0] : marks[marks.length - 1];
  return marks[(at + step + marks.length) % marks.length];
}

// Counts of recorded outcomes. These summarize what the report says, and say
// nothing about claims a function result does not cover.
function summarize(functions: any) {
  const tally = {
    functions: functions.length,
    gaps: 0,
    status: {} as Record<string, number>,
  };
  for (const f of functions) {
    tally.status[f.status] = (tally.status[f.status] || 0) + 1;
    tally.gaps += (f.gaps || []).length;
  }
  return tally;
}

// A report link names the source file and optionally one mark. It is a request
// to reopen that view, never a record that anything was established. Older links
// carrying a verify flag still work: verification is no longer optional, so the
// flag is read and ignored.
function parseReportLink(search: any, hash: any) {
  const params = new URLSearchParams(search || "");
  return {
    file: params.get("file") || "",
    mark: (hash || "").replace(/^#/, "") || "",
  };
}

function reportLink({ file, mark }: { file?: string; mark?: string }) {
  const params = new URLSearchParams();
  if (file) params.set("file", file);
  const query = params.toString();
  return (query ? "?" + query : "") + (mark ? "#" + mark : "");
}

export {
    signatureText,
    parseReport,
    fromBundle,
    renderType,
    findMark,
    markIdOf,
    nextMark,
    summarize,
    parseReportLink,
    reportLink,
};