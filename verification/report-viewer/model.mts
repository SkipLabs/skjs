import type { ObligationView } from "../tools/diagnostic-view.mts";
// Surface type printing is shared with the report writer.
import type { Bundle, Producer } from "./types.ts";
import type { Span } from "../tools/span.mts";

/*
 * What the reader shows for one function: the places it can point at, and the
 * one failure the verifier reported, if it did. Every field here is read by a
 * view or a suite; the manifest keeps everything else.
 */

/** One binding of an environment. */
export interface ShownBinding {
  name: string;
  /** Surface syntax, printed from the producer's encoding. */
  type: string;
  /** The producer could not decode its type. */
  unavailable: boolean;
}

/** A place in the function the reader can point at. */
export type Site =
  | {
      /** The result the function must establish, at the source's annotation. */
      kind: "result";
      pos: Span;
      /** Surface syntax, printed from the producer's claimed result. */
      type: string;
    }
  | {
      kind: "expression";
      pos: Span;
      /** Surface syntax, printed from the producer's encoding. */
      type: string;
      /** The producer's encoding as formatted JSON, for the inspector. */
      raw: string | null;
      recovery: boolean;
    }
  | {
      kind: "environment";
      pos: Span;
      bindings: ShownBinding[];
      /** Names whose type differs from the previous environment's. */
      changed: Set<string>;
      recovery: boolean;
    }
  | {
      kind: "unclaimed";
      pos: Span;
      /** What belongs here, where the lowering attaches a claim: it can be added. */
      claims?: "expression" | "environment";
      /** Why nothing is claimed, as the report's slug, and as its prose. */
      reason: string;
      detail: string;
    };

/** The function's one failure: what stopped, and where it attached. */
export interface Failure {
  detail: string;
  /** The location kind the verifier reported. */
  kind: string;
  role: string;
  binding: string;
  /** The site it attached to, or null where nothing is claimed at its place. */
  at: number | null;
  /** Where, when it has a place at all. */
  pos: Span | null;
  /** Both ends of an edge obligation, as sites, where the report maps them. */
  edge?: { from: number | null; to: number | null };
}

/** One function of the report, with everything the view draws for it. */
export interface ShownFunction {
  id: string;
  name: string;
  namePos?: Span;
  pos: Span;
  /** In source order: environments before expressions at the same offset. */
  sites: Site[];
  failure?: Failure;
  /** The verifier's verdict over this function's claims. */
  status: string;
  /** What the report says about it, where there is no result to report. */
  detail?: string;
  /** The producer's own collection outcome and its quality. */
  collection?: string;
  quality?: string;
  /** The obligation record, kept as recorded for the panel; never evidence. */
  obligation?: unknown;
  obligationView?: ObligationView;
  /** True for a source function the candidate says nothing about at all. */
  candidateMissing?: boolean;
  /** Its parameter names, in source order, for the contract it needs. */
  parameters?: string[];
}

/** Sites in source order, an environment before the claims of its statement. */
const RANK = { result: 0, environment: 0, expression: 1, unclaimed: 2 };
function ordered(sites: Site[]): Site[] {
  sites.sort((x, y) => x.pos[0] - y.pos[0] || RANK[x.kind] - RANK[y.kind]);
  let previous = new Map<string, string>();
  for (const s of sites) {
    if (s.kind !== "environment") continue;
    s.changed = new Set(s.bindings.filter((b) => previous.get(b.name) !== b.type).map((b) => b.name));
    previous = new Map(s.bindings.map((b) => [b.name, b.type]));
  }
  return sites;
}

export interface Report {
  source: string;
  producer: Producer | string;
  functions: ShownFunction[];
  diagnostics?: string;
  missingFunctions?: { name: string; namePos: Span }[];
}


import SURFACE from "../tools/claim-text.mts";
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
        status: "not-run",
        detail: "",
        collection: "",
        quality: "",
        sites: [] as Site[],
      } as Record<string, any>;
      for (const p of parts.slice(1)) {
        if (p.startsWith("verification=")) f.status = p.slice(13).trim();
        else if (p.startsWith("collection=")) f.collection = p.slice(11).trim();
        else if (p.startsWith("quality=")) f.quality = p.slice(8).trim();
        // The producer, the claimed signature and the mode are provenance the
        // manifest carries; nothing here reads them.
        else if (/^(producer=|claimed |mode=)/.test(p)) continue;
        else f.detail = (f.detail ? f.detail + "; " : "") + p;
      }
      f.id = fld.id || "";
      f.pos = [src.length, src.length];
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
          unavailable: unavailable.has(name) || ty.text === "unsupported",
        };
      });
      if (cur && pos)
        cur.sites.push({ kind: "environment", pos, bindings, recovery, changed: new Set() });
    } else if (kind === "expression") {
      const ty = renderType(core.replace(/^expr\s+/, ""));
      if (cur && pos)
        cur.sites.push({ kind: "expression", pos, type: ty.text, raw: ty.raw, recovery });
    } else if (pos && cur) {
      // a gap is a place the producer entered but did not claim, or an edit
      // against a baseline. Its reason is a slug; the prose is the long form.
      cur.sites.push({ kind: "unclaimed", pos, detail: core, reason: fld.reason || "" });
    }
  }
  src += annotated.slice(last);
  rep.source = src;
  for (let i = 0; i < rep.functions.length; i++) {
    rep.functions[i].pos[1] = rep.functions[i + 1]?.pos[0] ?? src.length;
    ordered(rep.functions[i].sites);
  }
  return rep;
}

function fromBundle(bundle: any) {
  const { source, manifest: m } = bundle;
  if (typeof source !== "string" || !Array.isArray(m?.functions))
    throw new Error("Expected source text and a report manifest");
  const span = (pos: any): Span => {
    if (
      !Array.isArray(pos) ||
      pos.length !== 2 ||
      !pos.every(Number.isSafeInteger) ||
      pos[0] < 0 ||
      pos[0] >= pos[1] ||
      pos[1] > source.length
    )
      throw new Error("Invalid claim source span");
    return pos as Span;
  };
  const sameSpan = (a: Span, b: Span) => a[0] === b[0] && a[1] === b[1];
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
    ...(m.comparison?.changes || []).map((c: any) => ({
      pos: c.span,
      status: `claim edit: ${c.status} ${c.kind}`,
    })),
  ];
  // A gap and a site the lowering attaches a claim to can be the same place:
  // "the producer did not visit this statement" and "this statement has no
  // environment claim" are one fact in two vocabularies, so it is one site,
  // with the gap's wording and the lowering's answer to what belongs there.
  const unclaimed = (f: any, pos: Span): Site[] => {
    const sites: Site[] = (f.missingSites || []).map((site: any) => {
      if (!["expression", "environment"].includes(site.kind))
        throw new Error("Invalid missing claim kind");
      span(site.pos);
      if (site.pos[0] < pos[0] || site.pos[1] > pos[1])
        throw new Error("Missing site outside function");
      return { kind: "unclaimed", pos: site.pos, claims: site.kind, reason: "", detail: "" };
    });
    for (const g of gaps) {
      if (!(g.pos[0] >= pos[0] && g.pos[1] <= pos[1])) continue;
      const at = span(g.pos);
      const reason = g.status === "statement not visited" ? "statement-not-visited" : "";
      const same = sites.find((s) => sameSpan(s.pos, at));
      if (same) Object.assign(same, { reason, detail: g.status });
      else sites.push({ kind: "unclaimed", pos: at, reason, detail: g.status });
    }
    return sites;
  };
  const functions: any[] = m.functions.map((f: any) => {
    const pos = span(f.pos);
    const result = m.results?.find((r: any) => r.function === f.id);
    const recovery = f.collection?.quality === "recovery";
    const sites: Site[] = [
      ...(Array.isArray(f.resultPos) && f.signature
        ? [{ kind: "result" as const, pos: span(f.resultPos), type: display(f.signature.retType, "") }]
        : []),
      ...f.entries.map((e: any) => ({
        kind: "environment" as const,
        pos: span(e.pos),
        recovery,
        changed: new Set<string>(),
        bindings: e.bindings.map((b: any) => ({
          name: b.name,
          type: display(b.raw, b.type),
          unavailable: b.raw?.unsupported === true || typeof b.raw?.unavailable === "string",
        })),
      })),
      ...f.expressions.map((e: any) => ({
        kind: "expression" as const,
        pos: span(e.pos),
        recovery,
        type: display(e.raw, e.type),
        raw: raw(e.raw),
      })),
      ...unclaimed(f, pos),
    ];
    return {
      id: f.id,
      name: f.name,
      namePos: f.namePos,
      pos,
      sites: ordered(sites),
      status: result?.status || "not-run",
      // The diagnostic is what a reader needs; the whole record stays available
      // for provenance, and neither is evidence.
      detail: result?.detail || "",
      // Explanatory metadata about an unsuccessful attempt, kept as recorded.
      obligation: result?.obligation || null,
      obligationView: result?.obligationView,
      collection: f.collection?.completion || "",
      quality: f.collection?.quality || "",
    };
  });
  for (const f of functions) {
    const result = m.results?.find((r: any) => r.function === f.id);
    const location = result?.location;
    if (f.status !== "not-established" || !location) continue;
    const sites: Site[] = f.sites;
    // Where a location does not land on a claim, the record's own environment
    // offset says which statement entry it belongs to.
    const entryStart =
      result.obligation?.destination?.sourceMap?.environmentStart ??
      result.obligation?.source?.sourceMap?.environmentStart ??
      location.start ??
      (Array.isArray(location.pos) ? location.pos[0] : undefined);
    const samePos = (s: Site) =>
      location.pos !== undefined && JSON.stringify(s.pos) === JSON.stringify(location.pos);
    const startsAt = (start: any) => (s: Site) => s.pos[0] === start;
    const is = (kind: Site["kind"], test: (s: Site) => boolean) => (s: Site) =>
      s.kind === kind && test(s);
    const first = (...tests: ((s: Site) => boolean)[]) => {
      for (const test of tests) {
        const i = sites.findIndex(test);
        if (i >= 0) return i;
      }
      return -1;
    };
    const at =
      // A required type the producer never decoded: no obligation was reached,
      // so this attaches to the claim that is missing one, not to a judgement.
      location.kind === "unavailable-type-claim"
        ? location.start !== undefined
          ? first(is("environment", startsAt(location.start)))
          : first(is("expression", samePos))
        : // A claim the verifier needed and did not find belongs on the site that
          // already marks that place. Falling back to a claim at the same
          // position keeps older reports, where no gap was recorded, locatable.
          location.kind === "missing-expression-claim"
          ? first(is("unclaimed", samePos), is("expression", samePos))
          : location.kind === "missing-environment-claim"
            ? first(is("unclaimed", startsAt(location.start)), is("environment", startsAt(location.start)))
            : location.kind === "environment-obligation"
              ? first(is("environment", startsAt(location.start)))
              : // A parameter claim contradicting its annotation: the first
                // environment that names the parameter is where the reader sees it.
                location.kind === "parameter-claim"
                ? first(
                    (s) => s.kind === "environment" && s.bindings.some((b) => b.name === location.binding),
                  )
                : ["expression-obligation", "edge-obligation", "source-limitation"].includes(location.kind)
                  ? // A span names an expression claim when there is one. An edge into
                    // a statement checkpoint has none: its destination is the entry.
                    first(is("expression", samePos), is("environment", startsAt(entryStart)))
                  : -1;
    // Which obligation stopped here — a return contract at a return statement
    // is not the expression's own claim, even though they share a span. For an
    // edge, the role that describes where this attached is the destination's;
    // `source` describes the other end.
    const destination = result.obligation?.destination?.sourceMap;
    const role =
      (destination && at >= 0 && destination.environmentStart === sites[at]!.pos[0]
        ? destination.role
        : "") ||
      result.obligation?.source?.sourceMap?.role ||
      result.obligation?.sourceMap?.role ||
      "";
    // Both ends of an edge obligation are claims: an expression at the mapped
    // span, or the environment at the mapped statement entry.
    const endSite = (map: any) => {
      const pos = map?.pos;
      const i = first(
        (s) =>
          Array.isArray(pos) && pos.length === 2 && s.kind !== "unclaimed" && sameSpan(s.pos, pos as Span),
        is("environment", startsAt(map?.environmentStart)),
      );
      return i >= 0 ? i : null;
    };
    // A return contract is an edge too: from the returned expression to the
    // result the function must establish.
    const resultSite = sites.findIndex((s) => s.kind === "result");
    const edge =
      result.obligation?.kind === "edge-coverage"
        ? {
            from: endSite(result.obligation.source?.sourceMap),
            to: endSite(result.obligation.destination?.sourceMap),
          }
        : role === "return-contract" && at >= 0 && resultSite >= 0
          ? { from: at, to: resultSite }
          : undefined;
    // A failure with a position but nothing claimed there — a body that
    // completes, say — is still real and still locatable, so the view can mark
    // the place instead of only saying at the top that no location is available.
    f.failure = {
      detail: result.detail || "Proof search did not establish this obligation.",
      kind: location.kind,
      role,
      binding: location.binding || "",
      at: at >= 0 ? at : null,
      pos: at >= 0 ? sites[at]!.pos : Array.isArray(location.pos) ? span(location.pos) : null,
      ...(edge ? { edge } : {}),
    };
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
      id: `missing-${f.namePos[0]}`,
      name: f.name,
      namePos: f.namePos,
      pos,
      sites: ordered(unclaimed(f, pos)),
      candidateMissing: true,
      parameters: f.parameters,
      status: "not-established",
      detail:
        "No function candidate supplied. Add its contract before adding point claims.",
    });
  }
  functions.sort((a: any, b: any) => a.pos[0] - b.pos[0]);
  const unattached = gaps.filter(
    (g) => !functions.some((f: any) => g.pos[0] >= f.pos[0] && g.pos[1] <= f.pos[1]),
  );
  if (unattached.length)
    functions.push({
      id: "gaps",
      name: "Other coverage gaps",
      pos: [0, source.length],
      status: "not-established",
      sites: ordered(
        unattached.map((g) => ({ kind: "unclaimed", pos: span(g.pos), reason: "", detail: g.status })),
      ),
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

export { parseReport, fromBundle, renderType };
