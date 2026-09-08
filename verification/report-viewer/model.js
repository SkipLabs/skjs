"use strict";
/* ---------- reading the annotated format ---------- */
const RE_COMMENT = /\/\*\s*@verify-report([\s\S]*?)\*\//g;

function unescapeText(s) {
  try {
    return JSON.parse('"' + s.replace(/\n/g, " ") + '"');
  } catch (e) {
    return s;
  }
}

// split "a: T, b: U" on top-level commas (types may be raw JSON)
function splitTop(s, sep) {
  const out = [];
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

function renderType(text) {
  const value = (text || "").trim();
  // Display text is already produced by the report writer. Never reinterpret
  // unknown producer encodings as a different type.
  return { text: value, raw: value.startsWith("{") ? value : null };
}

function parseReport(annotated) {
  const rep = {
    producer: "unknown",
    file: "(unknown source)",
    meta: {},
    functions: [],
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
    const fld = {};
    core = core
      .replace(/^(?:[a-z]+=[^;]*; )+/, (run) => {
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
        gaps: [],
      };
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
      prev = new Map(e.bindings.map((b) => [b.name, b.type]));
    }
  }
  return rep;
}

function fromBundle(bundle) {
  const { source, manifest: m } = bundle;
  if (
    typeof source !== "string" ||
    m?.version !== 1 ||
    !Array.isArray(m.functions)
  )
    throw new Error("Expected source text and a version 1 report manifest");
  const span = (pos) => {
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
  const raw = (x) => (x === undefined ? null : JSON.stringify(x, null, 2));
  const gaps = [
    ...(m.gaps || []),
    ...(m.comparison?.changes || []).map((c, i) => ({
      id: `g${(m.gaps || []).length + i}`,
      pos: c.span,
      status: `claim edit: ${c.status} ${c.kind}`,
    })),
  ];
  const functions = m.functions.map((f) => {
    const pos = span(f.pos);
    const result = m.results?.find((r) => r.function === f.id);
    const recovery = f.collection?.quality === "recovery";
    return {
      ...f,
      start: pos[0],
      end: pos[1],
      signature: f.signature ? JSON.stringify(f.signature) : null,
      status: result?.status || "not-run",
      detail: result ? JSON.stringify(result) : "",
      collection: f.collection?.completion || "",
      quality: f.collection?.quality || "",
      mode: f.collection?.mode || "",
      entries: f.entries.map((e) => ({
        ...e,
        pos: span(e.pos),
        recovery,
        changed: new Set(),
        bindings: e.bindings.map((b) => ({
          ...b,
          raw: raw(b.raw),
          unavailable: b.raw?.unsupported === true,
        })),
      })),
      exprs: f.expressions.map((e) => ({
        ...e,
        pos: span(e.pos),
        recovery,
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
    f.entries.sort((a, b) => a.pos[0] - b.pos[0]);
    let previous = new Map();
    for (const e of f.entries) {
      e.changed = new Set(
        e.bindings
          .filter((b) => previous.get(b.name) !== b.type)
          .map((b) => b.name),
      );
      previous = new Map(e.bindings.map((b) => [b.name, b.type]));
    }
  }
  for (const f of functions) {
    const result = m.results?.find((r) => r.function === f.id);
    const location = result?.location;
    if (
      f.status === "not-established" &&
      location?.kind === "expression-obligation"
    ) {
      const failed = f.exprs.find(
        (e) => JSON.stringify(e.pos) === JSON.stringify(location.pos),
      );
      if (failed)
        failed.failure =
          result.detail || "Proof search did not establish this obligation.";
    }
  }
  functions.sort((a, b) => a.start - b.start);
  const unattached = gaps.filter(
    (g) => !functions.some((f) => g.pos[0] >= f.start && g.pos[1] <= f.end),
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
    meta: {
      "source-sha256": m.source.sha256,
      ...Object.fromEntries(
        Object.entries(m).filter(([key]) => key.endsWith("Sha256")),
      ),
    },
    manifest: m,
  };
}
if (typeof module !== "undefined")
  module.exports = { parseReport, fromBundle, renderType };
