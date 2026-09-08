"use strict";
/* ---------- state ---------- */
const state = {
  report: null,
  fn: 0,
  density: "key",
  unsupported: false,
  selected: null,
};
const el = (id) => document.getElementById(id);
// These colours summarize recorded outcomes, never authenticate proof evidence.
const statusClass = (s) =>
  s === "verified" ? "st-ok" : s === "not-run" ? "st-none" : "st-attn";
const store = {
  get(k, d) {
    try {
      const v = localStorage.getItem("crr:" + k);
      return v === null ? d : JSON.parse(v);
    } catch (e) {
      return d;
    }
  },
  set(k, v) {
    try {
      localStorage.setItem("crr:" + k, JSON.stringify(v));
    } catch (e) {}
  },
};
state.density = store.get("density", "key");
state.unsupported = store.get("uns", false);

// A binding the producer could not decode carries no claim. It is real information
// about coverage, but it is not a type, so it stays out of the default view.
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
const lineStarts = (src) => {
  const a = [0];
  for (let i = 0; i < src.length; i++) if (src[i] === "\n") a.push(i + 1);
  return a;
};
const esc = (s) =>
  String(s).replace(
    /[&<>"']/g,
    (c) =>
      ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" })[
        c
      ],
  );
const KW =
  /^(function|return|if|else|const|let|var|typeof|instanceof|new|class|interface|type|export|import|from|extends|implements|for|while|do|switch|case|default|break|continue|throw|try|catch|finally|this|void|as|in|of|async|await|yield)$/;
const TY =
  /^(string|number|boolean|null|undefined|never|unknown|any|true|false|object|symbol|bigint)$/;
function hi(line) {
  const re =
    /("(?:[^"\\]|\\.)*"|'(?:[^'\\]|\\.)*'|`(?:[^`\\]|\\.)*`|\/\/[^\n]*|\b\d[\w.]*|[A-Za-z_$][\w$]*|\s+|[^\w\s]+)/g;
  let out = "",
    m;
  while ((m = re.exec(line))) {
    const s = m[0];
    let cls = "";
    if (/^["'`]/.test(s)) cls = "t-str";
    else if (s.startsWith("//")) cls = "t-com";
    else if (/^\d/.test(s)) cls = "t-num";
    else if (/^[A-Za-z_$]/.test(s))
      cls = KW.test(s) ? "t-kw" : TY.test(s) ? "t-ty" : "";
    else if (!/^\s+$/.test(s)) cls = "t-punct";
    out += cls ? '<span class="' + cls + '">' + esc(s) + "</span>" : esc(s);
  }
  return out;
}

/* ---------- source view ---------- */
// Claims are drawn as brackets under the exact span they are about, packed onto
// as few rows as fit. Nesting is then visible without hovering.
function bracket(w) {
  if (w <= 1) return "╵";
  return "╰" + "─".repeat(Math.max(0, w - 2)) + "╯";
}
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
    row.free = it.col + Math.max(1, it.end - it.col) + 1 + it.label.length + 1;
  }
  return rows;
}
function renderCode() {
  const rep = state.report,
    f = rep.functions[state.fn];
  const starts = lineStarts(rep.source);
  const lineOfPos = (p) => lineAt(starts, p);
  const allRecovery = f.quality === "recovery";
  const recMark = allRecovery ? "" : "  (recovery)";
  const items = [];
  f.exprs.forEach((e, i) => {
    if (!e.pos) return;
    const shown = rep.source.slice(e.pos[0], e.pos[1]);
    const failed = f.status === "not-established" && !!e.failure;
    if (state.density === "key" && !failed) {
      if (
        f.exprs.some(
          (other) =>
            other !== e &&
            other.pos &&
            other.pos[0] <= e.pos[0] &&
            other.pos[1] >= e.pos[1] &&
            (other.pos[0] < e.pos[0] || other.pos[1] > e.pos[1]),
        )
      )
        return;
      if (shown.trim() === e.type.trim()) return; // a literal restating itself
    }
    const ln = lineOfPos(e.pos[0]);
    const multiline = lineOfPos(e.pos[1] - 1) !== ln;
    items.push({
      kind: "expr",
      line: ln,
      col: e.pos[0] - starts[ln],
      end: multiline
        ? (starts[ln + 1] ?? rep.source.length) - starts[ln] - 1
        : e.pos[1] - starts[ln],
      label:
        (failed ? "⚠ " : "") +
        shortType(e.type) +
        (failed ? " · proof not established" : "") +
        (multiline ? " ↳ multiline" : "") +
        (e.recovery ? recMark : ""),
      id: "e" + i,
      cls: "expr" + (e.recovery ? " rec" : "") + (failed ? " failed" : ""),
    });
  });
  f.gaps.forEach((g, i) => {
    // always shown: absence is the finding
    const ln = lineOfPos(g.pos[0]);
    const end =
      lineOfPos(g.pos[1] - 1) === ln
        ? g.pos[1] - starts[ln]
        : (ln + 1 < starts.length ? starts[ln + 1] - 1 : rep.source.length) -
          starts[ln];
    items.push({
      kind: "gap",
      line: ln,
      col: g.pos[0] - starts[ln],
      end,
      label: gapLabel(g),
      id: "g" + i,
      cls: "gap",
    });
  });
  const entryItems = [];
  f.entries.forEach((e, i) => {
    if (!e.pos) return;
    const shown = e.bindings.filter((b) => state.unsupported || !isNoise(b));
    const list =
      state.density === "key"
        ? shown.filter((b) => e.changed.has(b.name))
        : shown;
    if (!list.length) return;
    const ln = lineOfPos(e.pos[0]),
      col = e.pos[0] - starts[ln];
    entryItems.push({
      kind: "entry",
      line: ln,
      col,
      end: col,
      label:
        list.map((b) => b.name + ": " + shortType(b.type)).join(",  ") +
        (e.recovery ? recMark : ""),
      id: "n" + i,
      cls: "entry" + (e.recovery ? " rec" : ""),
    });
  });

  const entryRows = groupLines(entryItems);
  const claimRows = groupLines(items);
  const gutter = String(starts.length).length + 1;
  const pad = (n) => " ".repeat(Math.max(0, n));
  const num = (n) =>
    '<span class="num">' + pad(gutter - String(n).length) + n + " </span>";
  const blank = '<span class="num">' + pad(gutter + 1) + "</span>";
  let out = "";
  for (
    let ln = lineOfPos(f.start || 0);
    ln <= lineOfPos(Math.max(0, (f.end ?? rep.source.length) - 1));
    ln++
  ) {
    const from = starts[ln],
      to = ln + 1 < starts.length ? starts[ln + 1] - 1 : rep.source.length;
    const text = rep.source.slice(from, to);
    if (ln === starts.length - 1 && text === "") break;
    for (const row of packRows(entryRows.get(ln) || []))
      out += blank + rowText(row.items) + "\n";
    out += num(ln + 1) + hi(text) + "\n";
    for (const row of packRows(claimRows.get(ln) || []))
      out += blank + rowText(row.items) + "\n";
  }
  el("code").innerHTML = '<pre class="pre">' + out + "</pre>";
  const warning = el("verification-warning");
  warning.hidden = f.status !== "not-established";
  if (!warning.hidden) {
    const failed = f.exprs.findIndex((e) => e.failure);
    warning.textContent =
      failed >= 0
        ? "⚠ Proof not established at the marked expression. Other claims are not individually classified."
        : "⚠ Function verification not established. The verifier has not identified a source expression to mark.";
    if (failed >= 0) {
      const jump = document.createElement("button");
      jump.textContent = "Show failed obligation";
      jump.addEventListener("click", () => {
        select("e" + failed);
        el("code")
          .querySelector('[data-id="e' + failed + '"]')
          ?.scrollIntoView({ block: "center" });
      });
      warning.append(jump);
    }
  }
  el("codehead").textContent = "Source — " + rep.file.split("/").pop();
  document.querySelectorAll(".lab").forEach((b) => {
    b.addEventListener("click", () => select(b.dataset.id));
    b.addEventListener("keydown", (ev) => {
      if (ev.key === "Enter" || ev.key === " ") {
        ev.preventDefault();
        select(b.dataset.id);
      }
    });
  });
}
function rowText(items) {
  let out = "",
    cur = 0;
  for (const it of items) {
    out += " ".repeat(Math.max(0, it.col - cur));
    const w = Math.max(1, it.end - it.col);
    out +=
      '<span class="br' +
      (it.kind === "gap" ? " gapbr" : "") +
      '">' +
      bracket(w) +
      "</span> ";
    out +=
      '<span class="lab ' +
      it.cls +
      '" data-id="' +
      it.id +
      '" role="button" tabindex="0">' +
      esc(it.label) +
      "</span>";
    cur = it.col + w + 1 + it.label.length;
  }
  return out;
}

/* ---------- narrowing table ---------- */
function renderFlow() {
  const f = state.report.functions[state.fn];
  const starts = lineStarts(state.report.source);
  const lineOf = (p) => lineAt(starts, p) + 1;
  const entries = f.entries.filter((e) => e.pos);
  if (!entries.length) {
    el("flow").innerHTML =
      '<div class="empty">No environment claims in this function.</div>';
    return;
  }
  const names = [];
  for (const e of entries)
    for (const b of e.bindings)
      if ((state.unsupported || !isNoise(b)) && !names.includes(b.name))
        names.push(b.name);
  let h =
    "<table><thead><tr><th>at</th>" +
    names.map((n) => "<th>" + esc(n) + "</th>").join("") +
    "</tr></thead><tbody>";
  const prev = new Map();
  for (const e of entries) {
    h +=
      '<tr><td class="bind"><button data-entry="' +
      f.entries.indexOf(e) +
      '">line ' +
      lineOf(e.pos[0]) +
      "</button></td>";
    for (const nm of names) {
      const b = e.bindings.find((x) => x.name === nm);
      const t = b ? b.type : "—";
      const cls = b && t !== prev.get(nm) ? "chg" : "same";
      h += '<td class="' + cls + '">' + esc(t) + "</td>";
      if (b) prev.set(nm, t);
    }
    h += "</tr>";
  }
  h += "</tbody></table>";
  el("flow").innerHTML = h;
  el("flow")
    .querySelectorAll("[data-entry]")
    .forEach((b) =>
      b.addEventListener("click", () => select("n" + b.dataset.entry)),
    );
}

/* ---------- selection detail ---------- */
// The id joins this mark to its record in the companion JSON manifest.
const idLine = (item) =>
  item.id
    ? '<div class="status-line">manifest id <b>' + esc(item.id) + "</b></div>"
    : "";
function select(id) {
  const f = state.report.functions[state.fn];
  const idx = +id.slice(1);
  const item =
    id[0] === "e"
      ? { kind: "expression", ...f.exprs[idx] }
      : id[0] === "g"
        ? { kind: "gap", ...f.gaps[idx] }
        : { kind: "environment", ...f.entries[idx] };
  state.selected = item;
  el("inspector").scrollIntoView({ block: "nearest" });
  const src = state.report.source;
  let h = "";
  if (f.status === "not-established" && item.failure)
    h +=
      '<div class="failure-note"><b>⚠ Proof not established here</b><p>This identifies the expression obligation where proof search stopped. It does not prove the claim false; its environment or source annotation may also be involved.</p><pre class="raw">' +
      esc(item.failure) +
      "</pre></div>";
  if (item.kind === "gap") {
    h += '<div class="status-line"><b>' + esc(item.detail) + "</b></div>";
    h += idLine(item);
    h +=
      '<pre class="raw">' + esc(src.slice(item.pos[0], item.pos[1])) + "</pre>";
    h +=
      '<div class="note">This report marks a gap or change: ' +
      "collection, conversion, or comparison left a finding. This does not establish runtime unreachability or verification failure.</div>";
    el("detail").innerHTML = h;
    renderMissingEditor(f,item.pos);
    document
      .querySelectorAll(".lab")
      .forEach((x) => x.classList.toggle("on", x.dataset.id === id));
    return;
  }
  if (item.kind === "expression") {
    h += '<div class="status-line"><b>' + esc(item.type) + "</b></div>";
    h +=
      '<pre class="raw">' + esc(src.slice(item.pos[0], item.pos[1])) + "</pre>";
    h +=
      '<dl class="kv"><dt>kind</dt><dd>expression</dd><dt>span</dt><dd>' +
      item.pos[0] +
      "–" +
      item.pos[1] +
      "</dd>" +
      (item.id ? "<dt>id</dt><dd>" + esc(item.id) + "</dd>" : "") +
      "</dl>";
    if (item.recovery)
      h +=
        '<div class="note">Recovery claim: from a recovery-quality snapshot. ' +
        "Displayed for orientation, never as evidence.</div>";
    const entry = f.entries
      .filter(
        (e) => e.pos && e.pos[0] <= item.pos[0] && e.pos[1] >= item.pos[1],
      )
      .sort((a, b) => a.pos[1] - a.pos[0] - (b.pos[1] - b.pos[0]))[0];
    if (entry)
      h +=
        '<details open><summary>Containing statement entry claims</summary><pre class="raw">' +
        esc(
          entry.bindings
            .filter((b) => state.unsupported || !isNoise(b))
            .map((b) => b.name + ": " + b.type)
            .join("\n"),
        ) +
        "</pre></details>";
    const nested = f.exprs
      .map((e, i) => ({ e, i }))
      .filter(
        ({ e }) =>
          e.pos[0] >= item.pos[0] &&
          e.pos[1] <= item.pos[1] &&
          e.id !== item.id,
      );
    if (nested.length)
      h +=
        "<details><summary>Nested expression claims (" +
        nested.length +
        ")</summary>" +
        nested
          .map(
            ({ e, i }) =>
              '<button data-nested="e' +
              i +
              '">' +
              esc(src.slice(...e.pos)) +
              " : " +
              esc(shortType(e.type)) +
              "</button>",
          )
          .join("") +
        "</details>";
    if (item.raw)
      h +=
        '<details class="disc"><summary>producer encoding</summary><pre class="raw">' +
        esc(item.raw) +
        "</pre></details>";
  } else {
    h +=
      '<div class="status-line">environment at <b>character ' +
      item.pos[0] +
      "</b></div>";
    h += idLine(item);
    h += '<dl class="kv">';
    for (const b of item.bindings) {
      if (!state.unsupported && isNoise(b)) continue;
      h +=
        "<dt>" +
        esc(b.name) +
        "</dt><dd>" +
        esc(b.type) +
        (item.changed.has(b.name)
          ? " ←changed from preceding source entry"
          : "") +
        "</dd>";
    }
    h += "</dl>";
    const raws = item.bindings.filter((b) => b.raw);
    if (raws.length)
      h +=
        '<details class="disc"><summary>producer encoding</summary><pre class="raw">' +
        esc(raws.map((b) => b.name + ": " + b.raw).join("\n")) +
        "</pre></details>";
  }
  el("detail").innerHTML = h;
  renderEditor(f, item);
  el("detail")
    .querySelectorAll("[data-nested]")
    .forEach((b) =>
      b.addEventListener("click", () => select(b.dataset.nested)),
    );
  document
    .querySelectorAll(".lab")
    .forEach((x) => x.classList.toggle("on", x.dataset.id === id));
}

/* ---------- header, functions, provenance ---------- */
function renderShell() {
  const rep = state.report;
  el("srcline").innerHTML =
    "<b>" +
    esc(rep.file) +
    "</b> · producer " +
    esc(rep.producer) +
    (rep.sample
      ? ' · <span class="sample-note">' + esc(rep.sample) + "</span>"
      : "");
  el("diagnostics").textContent =
    rep.diagnostics || "No diagnostic text in this report.";
  el("fnstrip").innerHTML = rep.functions
    .map(
      (f, i) =>
        '<button class="fn-pill ' +
        statusClass(f.status) +
        '" data-i="' +
        i +
        '" type="button" aria-pressed="' +
        (i === state.fn) +
        '">' +
        '<i class="dot"></i><span class="nm">' +
        esc(f.name) +
        "</span>" +
        '<span class="sig">' +
        esc(f.status) +
        "</span>" +
        (f.collection && f.collection !== "complete"
          ? '<span class="sig warn">claims ' + esc(f.collection) + "</span>"
          : "") +
        (f.gaps.length
          ? '<span class="sig warn">' +
            f.gaps.length +
            " gap" +
            (f.gaps.length > 1 ? "s" : "") +
            "</span>"
          : "") +
        "</button>",
    )
    .join("");
  el("fnstrip")
    .querySelectorAll(".fn-pill")
    .forEach((b) =>
      b.addEventListener("click", () => {
        state.fn = +b.dataset.i;
        state.selected = null;
        el("detail").innerHTML =
          '<div class="empty">Select a claim in the source to see its span and the raw producer encoding.</div>';
        renderShell();
        renderCode();
        renderFlow();
      }),
    );
  filterFunctions();
  const f = rep.functions[state.fn];
  let p =
    '<div class="status-line ' +
    statusClass(f ? f.status : "") +
    '"><i class="dot"></i> verification <b>' +
    esc(f ? f.status : "—") +
    "</b> (recorded result)</div>";
  if (f?.signature)
    p +=
      '<details><summary>Producer function signature</summary><pre class="raw">' +
      esc(f.signature) +
      "</pre></details>";
  if (f && f.detail)
    p += '<div class="status-line">' + esc(f.detail) + "</div>";
  if (f && f.collection)
    p +=
      '<dl class="kv"><dt>claims</dt><dd>' +
      esc(f.collection) +
      (f.quality ? " · " + esc(f.quality) : "") +
      (f.mode ? " · " + esc(f.mode) : "") +
      "</dd></dl>";
  p += '<details><summary>Snapshot fingerprints</summary><dl class="kv">';
  for (const [k, v] of Object.entries(rep.meta))
    p +=
      "<dt>" +
      esc(k.replace(/Sha256$/, " sha256").replace(/-/g, " ")) +
      "</dt><dd>" +
      esc(v.length > 18 ? v.slice(0, 12) + "…" + v.slice(-4) : v) +
      "</dd>";
  p += "</dl></details>";
  p +=
    '<details class="disc"><summary>what a status means</summary><div class="detail" style="padding:8px 0 0">' +
    "<div><b>verified</b> — a certificate for this function was checked by the independent consumer.</div>" +
    "<div><b>not-run</b> — claims are displayed only; no verification was requested.</div>" +
    "<div>Results cover modeled obligations, not every exported claim.</div></div></details>";
  el("prov").innerHTML = p;
}

let loadVersion = 0;
async function load(text, isSample, sampleNote, keepCandidate = false) {
  if (!keepCandidate && !canReplaceCandidate()) return;
  const version = ++loadVersion;
  try {
    const input =
      typeof text === "string" && text.trim().startsWith("{")
        ? JSON.parse(text)
        : text;
    if (typeof input !== "string") {
      const digest = await crypto.subtle.digest(
        "SHA-256",
        new TextEncoder().encode(input.source),
      );
      const hash = Array.from(new Uint8Array(digest), (b) =>
        b.toString(16).padStart(2, "0"),
      ).join("");
      if (version !== loadVersion) return;
      if (
        input.candidate &&
        (hash !== input.candidate.sourceSha256 ||
          input.candidate.file !== input.manifest?.source?.file)
      )
        throw new Error("Candidate source identity mismatch");
      if (hash !== input.manifest?.source?.sha256)
        throw new Error("Source fingerprint mismatch");
    }
    const rep =
      typeof input === "string" ? parseReport(input) : fromBundle(input);
    if (!rep.functions.length)
      throw new Error("no @verify-report function annotations found");
    rep.sample = isSample ? sampleNote || "sample report" : null;
    if (!keepCandidate) {
      candidateState.candidate =
        typeof input === "object" && input.candidate
          ? structuredClone(input.candidate)
          : null;
      candidateState.original = candidateState.candidate
        ? structuredClone(input.originalCandidate || input.candidate)
        : null;
      candidateState.saved = JSON.stringify(candidateState.candidate);
      candidateState.revision++;
    }
    candidateState.bundle = typeof input === "object" ? input : null;
    state.report = rep;
    if (input.draftUnrendered)
      for (const f of rep.functions) {
        f.status = "stale";
        f.detail =
          "Saved draft differs from this last successful preview. Apply or verify the candidate.";
      }
    state.fn = 0;
    state.selected = null;
    el("fnsearch").value = "";
    if (!isSample)
      for (const id of ["s-clean", "s-gaps"])
        el(id).setAttribute("aria-pressed", "false");
    el("detail").innerHTML =
      '<div class="empty">Select a claim in the source to see its span and the raw producer encoding.</div>';
    renderShell();
    renderCode();
    renderFlow();
    renderCandidateStatus();
  } catch (err) {
    if (version !== loadVersion) return;
    state.report = null;
    el("candidate-panel").hidden = true;
    for (const id of ["fnstrip", "flow", "detail", "prov", "diagnostics"])
      el(id).replaceChildren();
    el("code").innerHTML =
      '<div class="empty">Could not read that file: ' +
      esc(err.message) +
      ". Expected an annotated .ts written by annotate-source.js.</div>";
  }
}

/* ---------- controls ---------- */
function setDensity(d) {
  state.density = d;
  store.set("density", d);
  el("d-key").setAttribute("aria-pressed", String(d === "key"));
  el("d-all").setAttribute("aria-pressed", String(d === "all"));
  if (state.report) renderCode();
}
el("d-key").addEventListener("click", () => setDensity("key"));
el("d-all").addEventListener("click", () => setDensity("all"));
el("t-uns").checked = state.unsupported;
el("t-uns").addEventListener("change", (e) => {
  state.unsupported = e.target.checked;
  store.set("uns", state.unsupported);
  if (state.report) {
    renderCode();
    renderFlow();
  }
});
el("load").addEventListener("click", () => el("file").click());
el("file").addEventListener("change", (e) => {
  const f = e.target.files[0];
  if (!f) return;
  f.text().then((t) => {
    activeRequest++;
    document.body.classList.remove("busy");
    return load(t, false);
  });
});
const drop = el("drop");
window.addEventListener("dragover", (e) => {
  e.preventDefault();
  drop.classList.add("on");
});
window.addEventListener("dragleave", (e) => {
  if (e.relatedTarget === null) drop.classList.remove("on");
});
window.addEventListener("drop", (e) => {
  e.preventDefault();
  drop.classList.remove("on");
  const f = e.dataTransfer.files[0];
  if (f)
    f.text().then((t) => {
      activeRequest++;
      document.body.classList.remove("busy");
      return load(t, false);
    });
});

// ---- live companion: run SKJS and the annotator from the page ----
let activeRequest = 0;
async function connectLive() {
  try {
    const h = await fetch("api/health", { cache: "no-store" });
    if (!h.ok) return;
    const info = await h.json();
    const r = await fetch("api/files", { cache: "no-store" });
    const { files } = await r.json();
    if (!files.length) return;
    const sel = el("livefile");
    sel.innerHTML =
      '<option value="">Open source…</option>' +
      files
        .map(
          (f) =>
            '<option value="' +
            esc(f) +
            '">' +
            esc(f.replace(/^verification\/tests\//, "")) +
            "</option>",
        )
        .join("");
    el("livewrap").hidden = false;
    const wanted = new URLSearchParams(location.search).get("file");
    if (wanted) {
      if (!files.includes(wanted)) {
        const option = document.createElement("option");
        option.value = wanted;
        option.textContent = wanted;
        sel.append(option);
      }
      sel.value = wanted;
    }
    el("verifywrap").hidden = !info.verifier;
    const run = async () => {
      const file = sel.value;
      if (!file) return;
      if (!canReplaceCandidate()) {
        sel.value = state.report?.file || "";
        return;
      }
      const request = ++activeRequest;
      loadVersion++;
      document.body.classList.add("busy");
      el("codehead").textContent =
        "Running SKJS on " + file.split("/").pop() + "…";
      try {
        const q =
          "api/analyse?path=" +
          encodeURIComponent(file) +
          (el("liveverify").checked ? "&verify=1" : "");
        const res = await fetch(q, { cache: "no-store" });
        const data = await res.json();
        if (request !== activeRequest) return;
        if (data.error) throw new Error(data.error.split("\n")[0]);
        await load(data, false);
      } catch (err) {
        if (request !== activeRequest) return;
        state.report = null;
        for (const id of ["fnstrip", "flow", "detail", "prov", "diagnostics"])
          el(id).replaceChildren();
        el("code").innerHTML =
          '<div class="empty">' +
          esc(file) +
          " — " +
          esc(err.message) +
          "</div>";
        el("codehead").textContent = "Source";
      } finally {
        if (request === activeRequest) document.body.classList.remove("busy");
      }
    };
    sel.addEventListener("change", run);
    el("liveverify").addEventListener("change", () => {
      if (sel.value) run();
    });
    if (sel.value) run();
  } catch (e) {
    /* not served locally: samples and drag-and-drop only */
  }
}
connectLive();

setDensity(state.density);
function pickSample(which) {
  if (!canReplaceCandidate()) return;
  activeRequest++;
  document.body.classList.remove("busy");
  el("s-clean").setAttribute("aria-pressed", String(which === "clean"));
  el("s-gaps").setAttribute("aria-pressed", String(which === "gaps"));
  load(
    document.getElementById(which === "gaps" ? "sample2" : "sample")
      .textContent,
    true,
    which === "gaps"
      ? "real report for a program SKJS rejects"
      : "real report for a program SKJS accepts",
  );
}
el("s-clean").addEventListener("click", () => pickSample("clean"));
el("s-gaps").addEventListener("click", () => pickSample("gaps"));
pickSample("clean");

function shortType(type) {
  if (type.startsWith("{")) return "structured type — inspect";
  return type.length > 64 ? type.slice(0, 61) + "…" : type;
}
function filterFunctions() {
  const query = el("fnsearch").value.toLowerCase();
  el("fnstrip")
    .querySelectorAll("button")
    .forEach((button) => {
      button.hidden = !state.report.functions[+button.dataset.i].name
        .toLowerCase()
        .includes(query);
    });
}
el("fnsearch").addEventListener("input", filterFunctions);

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
function groupLines(items) {
  const grouped = new Map();
  for (const item of items) {
    if (!grouped.has(item.line)) grouped.set(item.line, []);
    grouped.get(item.line).push(item);
  }
  return grouped;
}

initializeCandidateEditor();
