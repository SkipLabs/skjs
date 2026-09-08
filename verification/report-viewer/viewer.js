"use strict";
/* ---------- state ---------- */
const state = {
  report: null,
  fn: 0,
  density: "key",
  unsupported: false,
  selected: null,
  selectedId: null,
  // Ids of the marks currently drawn, in reading order, for keyboard movement.
  marks: [],
  // A mark named by the URL, applied once the report it belongs to is rendered.
  pendingMark: parseReportLink(location.search, location.hash).mark,
  pendingFile: parseReportLink(location.search, location.hash).file,
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
state.producerErrors = store.get("errs", true);

// A binding the producer could not decode carries no claim. It is real information
// about coverage, but it is not a type, so it stays out of the default view.
// SKJS reports its own errors against the source, with 1-based columns and an
// exclusive end. They are the producer's diagnostics, shown where they point;
// nothing here is a claim or a verification result.
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
    const lineEnd =
      ln + 1 < starts.length ? starts[ln + 1] - 1 : rep.source.length;
    const start = Math.min(starts[ln] + Number(from) - 1, lineEnd);
    const end = Math.min(Math.max(starts[ln] + Number(to) - 1, start + 1), lineEnd);
    marks.push({ pos: [start, end], text: text.trim(), line: ln });
  }
  return marks;
}

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
// Block comments span lines, so highlighting carries state from one line to the
// next: a doc comment above a function must not be coloured as code.
function hi(line, state = { block: false }) {
  let out = "";
  if (state.block) {
    const close = line.indexOf("*/");
    const chunk = close < 0 ? line : line.slice(0, close + 2);
    out += '<span class="t-com">' + esc(chunk) + "</span>";
    if (close < 0) return out;
    state.block = false;
    line = line.slice(close + 2);
  }
  const re =
    /(\/\*[\s\S]*?\*\/|\/\*[\s\S]*$|"(?:[^"\\]|\\.)*"|'(?:[^'\\]|\\.)*'|`(?:[^`\\]|\\.)*`|\/\/[^\n]*|\b\d[\w.]*|[A-Za-z_$][\w$]*|\s+|[^\w\s]+)/g;
  let m;
  while ((m = re.exec(line))) {
    const s = m[0];
    let cls = "";
    if (s.startsWith("/*")) {
      if (!s.endsWith("*/")) state.block = true;
      cls = "t-com";
    } else if (/^["'`]/.test(s)) cls = "t-str";
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
        (failed
          ? e.failureKind === "source-limitation"
            ? " · unsupported source"
            : " · proof search failed"
          : "") +
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
    const needed = f.status === "not-established" && !!g.failure;
    items.push({
      kind: "gap",
      line: ln,
      col: g.pos[0] - starts[ln],
      end,
      label:
        (needed ? "⚠ " : "") +
        gapLabel(g) +
        (needed
          ? g.failureBinding
            ? " · verification needed a claim for " + g.failureBinding
            : " · verification needed a claim here"
          : ""),
      id: "g" + i,
      cls: "gap" + (needed ? " failed" : ""),
    });
  });
  if (state.producerErrors)
    for (const [i, mark] of producerMarks(rep).entries()) {
      if (mark.pos[0] < (f.start || 0) || mark.pos[1] > (f.end ?? rep.source.length))
        continue;
      const ln = lineOfPos(mark.pos[0]);
      items.push({
        kind: "error",
        line: ln,
        col: mark.pos[0] - starts[ln],
        end: Math.max(mark.pos[1] - starts[ln], mark.pos[0] - starts[ln] + 1),
        label: mark.text.length > 72 ? mark.text.slice(0, 69) + "…" : mark.text,
        id: "p" + i,
        cls: "err",
      });
    }
  const entryItems = [];
  f.entries.forEach((e, i) => {
    if (!e.pos) return;
    const shown = e.bindings.filter((b) => state.unsupported || !isNoise(b));
    const list =
      state.density === "key"
        ? shown.filter((b) => e.changed.has(b.name))
        : shown;
    const failed = f.status === "not-established" && !!e.failure;
    if (!list.length && !failed) return;
    const ln = lineOfPos(e.pos[0]),
      col = e.pos[0] - starts[ln];
    entryItems.push({
      kind: "entry",
      line: ln,
      col,
      end: col,
      label:
        (failed ? "⚠ " : "") +
        list.map((b) => b.name + ": " + shortType(b.type)).join(",  ") +
        (failed ? " · proof search failed" : "") +
        (e.recovery ? recMark : ""),
      id: "n" + i,
      cls: "entry" + (e.recovery ? " rec" : "") + (failed ? " failed" : ""),
    });
  });

  const entryRows = groupLines(entryItems);
  const claimRows = groupLines(items);
  const marks = [];
  const gutter = String(starts.length).length + 1;
  const pad = (n) => " ".repeat(Math.max(0, n));
  const num = (n) =>
    '<span class="num">' + pad(gutter - String(n).length) + n + " </span>";
  const blank = '<span class="num">' + pad(gutter + 1) + "</span>";
  let out = "";
  // Highlighting state runs down the rendered lines, not the whole file: a
  // function shown on its own starts outside any comment.
  const highlighting = { block: false };
  const previousEnd = rep.functions
    .filter((other) => other !== f && other.end <= (f.start || 0))
    .reduce((furthest, other) => Math.max(furthest, other.end), 0);
  for (
    let ln = commentStartLine(rep.source, starts, f.start || 0, previousEnd);
    ln <= lineOfPos(Math.max(0, (f.end ?? rep.source.length) - 1));
    ln++
  ) {
    const from = starts[ln],
      to = ln + 1 < starts.length ? starts[ln + 1] - 1 : rep.source.length;
    const text = rep.source.slice(from, to);
    if (ln === starts.length - 1 && text === "") break;
    for (const row of packRows(entryRows.get(ln) || [])) {
      out += blank + rowText(row.items) + "\n";
      marks.push(...row.items.map((it) => it.id));
    }
    out += num(ln + 1) + hi(text, highlighting) + "\n";
    for (const row of packRows(claimRows.get(ln) || [])) {
      out += blank + rowText(row.items) + "\n";
      marks.push(...row.items.map((it) => it.id));
    }
  }
  state.marks = marks;
  el("code").innerHTML = '<pre class="pre">' + out + "</pre>";
  const warning = el("verification-warning");
  warning.hidden = f.status !== "not-established";
  if (!warning.hidden) {
    const expression = f.exprs.findIndex((e) => e.failure);
    const entry = f.entries.findIndex((e) => e.failure);
    const gap = f.gaps.findIndex((g) => g.failure);
    const failedId =
      expression >= 0
        ? "e" + expression
        : entry >= 0
          ? "n" + entry
          : gap >= 0
            ? "g" + gap
            : null;
    const failureKind = (
      expression >= 0
        ? f.exprs[expression]
        : entry >= 0
          ? f.entries[entry]
          : gap >= 0
            ? f.gaps[gap]
            : {}
    ).failureKind;
    const missingClaim =
      failureKind === "missing-expression-claim" ||
      failureKind === "missing-environment-claim";
    warning.textContent =
      failureKind === "source-limitation"
        ? "⚠ Verification unavailable: the marked source expression is outside the supported fragment. This is not a verdict on your edited claim."
        : missingClaim
          ? "⚠ Verification needs a claim this report does not contain. The marked place is where extraction stopped, not a claim that was disproved."
          : failedId
            ? "⚠ Proof search failed at the marked obligation. Other claims are not individually classified."
            : "⚠ Proof search failed for this function. No claim location is available for this diagnostic.";
    if (failedId) {
      const jump = document.createElement("button");
      jump.textContent =
        failureKind === "source-limitation"
          ? "Show unsupported expression"
          : missingClaim
            ? "Show the missing claim"
            : "Show failed obligation";
      jump.addEventListener("click", () => {
        select(failedId);
        el("code")
          .querySelector('[data-id="' + failedId + '"]')
          ?.scrollIntoView({ block: "center" });
      });
      warning.append(jump);
    } else if (f.detail) {
      const detail = document.createElement("pre");
      detail.className = "raw";
      detail.textContent = f.detail;
      warning.append(detail);
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
      (it.kind === "gap" ? " gapbr" : it.kind === "error" ? " errbr" : "") +
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

/* ---------- addressing the current view ---------- */
// The URL names the file, whether verification was requested, and the selected
// mark by its manifest id, so a view can be reopened or quoted. A link is a
// request to display something; it carries no evidence about it.
function syncLocation() {
  const live = el("livewrap");
  const link = reportLink({
    file: live && !live.hidden ? el("livefile").value : "",
    mark: state.report
      ? markIdOf(state.report, state.fn, state.selectedId)
      : "",
  });
  if (!link && !location.search && !location.hash) return;
  try {
    history.replaceState(null, "", link || location.pathname);
  } catch (e) {
    // Some browsers refuse replaceState for local files; the fragment still works.
    if (link.includes("#")) location.hash = link.slice(link.indexOf("#") + 1);
  }
}

function clearSelection() {
  state.selected = null;
  state.selectedId = null;
  el("detail").innerHTML =
    '<div class="empty">Select a claim in the source to see its span and the raw producer encoding.</div>';
  document.querySelectorAll(".lab.on").forEach((x) => x.classList.remove("on"));
  syncLocation();
}

// Applies a mark named by the URL once its report is rendered. An unknown id is
// left alone rather than guessed at: ids identify records in one snapshot.
function applyPendingMark() {
  const wanted = state.pendingMark;
  if (!wanted || !state.report) return;
  // Reports arrive in any order. Wait for the file the link names rather than
  // applying its mark to whichever report renders first.
  if (state.pendingFile && state.report.file !== state.pendingFile) return;
  const found = findMark(state.report, wanted);
  // Keep the request until the report holding that id loads, or until the
  // reader asks for something else.
  if (!found) return;
  state.pendingMark = "";
  if (found.fn !== state.fn) {
    state.fn = found.fn;
    renderShell();
    renderCode();
    renderFlow();
  }
  if (found.id) {
    // A linked claim can be one Compact hides. Show every claim for this view
    // rather than selecting something the reader cannot see; the stored density
    // preference is left alone.
    if (!state.marks.includes(found.id)) setDensity("all", false);
    select(found.id);
    revealSelected();
  } else syncLocation();
}

function revealSelected() {
  el("code")
    .querySelector('[data-id="' + state.selectedId + '"]')
    ?.scrollIntoView({ block: "center", behavior: "auto" });
}

// Keyboard movement through the marks as drawn, so a dense report can be read
// without hunting for small labels with the mouse.
function moveSelection(step) {
  const next = nextMark(state.marks, state.selectedId, step);
  if (!next) return;
  select(next);
  revealSelected();
}

// Moves to the next function the caller's test accepts, after the current one,
// wrapping. Selects that function's first failure or gap when it has one.
function jumpToFunction(matches) {
  const fns = state.report?.functions || [];
  for (let i = 1; i <= fns.length; i++) {
    const at = (state.fn + i) % fns.length;
    if (!matches(fns[at])) continue;
    state.fn = at;
    state.selected = null;
    state.selectedId = null;
    renderShell();
    renderCode();
    renderFlow();
    const f = fns[at];
    const failed = f.exprs.findIndex((e) => e.failure);
    const failedEntry = f.entries.findIndex((e) => e.failure);
    const target =
      failed >= 0
        ? "e" + failed
        : failedEntry >= 0
          ? "n" + failedEntry
          : f.gaps.length
            ? "g0"
            : null;
    if (target && state.marks.includes(target)) {
      select(target);
      revealSelected();
    } else syncLocation();
    return;
  }
}

function moveFunction(step) {
  const count = state.report?.functions.length || 0;
  if (count < 2) return;
  state.fn = (state.fn + step + count) % count;
  state.selected = null;
  state.selectedId = null;
  el("detail").innerHTML =
    '<div class="empty">Select a claim in the source to see its span and the raw producer encoding.</div>';
  renderShell();
  renderCode();
  renderFlow();
  syncLocation();
}

document.addEventListener("keydown", (ev) => {
  if (ev.metaKey || ev.ctrlKey || ev.altKey || !state.report) return;
  const t = ev.target;
  if (
    t &&
    (t.isContentEditable ||
      ["INPUT", "TEXTAREA", "SELECT", "BUTTON"].includes(t.tagName))
  )
    return;
  const keys = {
    j: () => moveSelection(1),
    ArrowDown: () => moveSelection(1),
    k: () => moveSelection(-1),
    ArrowUp: () => moveSelection(-1),
    "]": () => moveFunction(1),
    "[": () => moveFunction(-1),
    Escape: () => clearSelection(),
  };
  const action = keys[ev.key];
  if (!action) return;
  ev.preventDefault();
  action();
});

/* ---------- selection detail ---------- */
// The id joins this mark to its record in the companion JSON manifest.
const idLine = (item) =>
  item.id
    ? '<div class="status-line">manifest id <b>' + esc(item.id) + "</b></div>"
    : "";
function select(id) {
  const f = state.report.functions[state.fn];
  state.selectedId = id;
  syncLocation();
  if (id[0] === "p") {
    const mark = producerMarks(state.report)[+id.slice(1)];
    state.selected = { kind: "producer-diagnostic", ...mark };
    el("detail").innerHTML =
      '<div class="status-line"><b>SKJS diagnostic</b></div>' +
      '<pre class="raw">' +
      esc(mark.text) +
      "</pre>" +
      '<pre class="raw">' +
      esc(state.report.source.slice(mark.pos[0], mark.pos[1])) +
      "</pre>" +
      '<div class="note">This is the producer reporting on its own run, not a ' +
      "claim and not a verification result. It depends on the source file only.</div>";
    document
      .querySelectorAll(".lab")
      .forEach((x) => x.classList.toggle("on", x.dataset.id === id));
    return;
  }
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
  if (f.status === "not-established" && item.failure) {
    const explanation =
      item.failureKind === "source-limitation"
        ? "Source conversion stopped at this unsupported expression, before checking the candidate’s proof obligations."
        : item.failureKind === "missing-expression-claim"
          ? "Extraction needed a claimed type for this expression and the report has none. Supplying one is what makes checking possible; it does not make the claim true."
          : item.failureKind === "missing-environment-claim"
            ? (item.failureBinding
                ? "The environment claimed at this statement does not include the binding ‘" +
                  esc(item.failureBinding) +
                  "’, which extraction needed."
                : "Extraction needed the environment claimed at this statement and the report has none.") +
              " Supplying it is what makes checking possible; it does not make the claim true."
        : item.failureKind === "edge-obligation"
          ? "An incoming edge did not justify the environment used at this expression. The incoming value or destination environment may be involved."
          : item.failureKind === "environment-obligation"
            ? "The verifier could not use this statement environment."
            : "This identifies the expression obligation where checking stopped. Its environment or source annotation may also be involved.";
    h +=
      '<div class="failure-note"><b>⚠ ' +
      (item.failureKind === "source-limitation"
        ? "Unsupported source expression"
        : item.failureKind === "missing-expression-claim" ||
            item.failureKind === "missing-environment-claim"
          ? "Verification needed a claim here"
          : "Proof search failed here") +
      "</b><p>" +
      explanation +
      ' This does not prove the claim false.</p><pre class="raw">' +
      esc(item.failure) +
      "</pre></div>";
  }
  if (item.kind === "gap") {
    h += '<div class="status-line"><b>' + esc(item.detail) + "</b></div>";
    h += idLine(item);
    h +=
      '<pre class="raw">' + esc(src.slice(item.pos[0], item.pos[1])) + "</pre>";
    h +=
      '<div class="note">This report marks a gap or change: ' +
      "collection, conversion, or comparison left a finding. This does not establish runtime unreachability or verification failure.</div>";
    el("detail").innerHTML = h;
    renderMissingEditor(f, item.pos);
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
// A stamp marks a function whose certificate the independent consumer checked
// for this report, in this session. A status that only comes from a file is
// shown as recorded, not stamped: a stored status is never evidence.
// Whether the producer actually ran for what is on screen, and when. A report
// read from a file carries no such record, and says so rather than implying one.
const clock = (iso) => {
  const at = new Date(iso);
  return Number.isNaN(at.getTime()) ? "" : at.toLocaleTimeString();
};
function collectedLine(rep) {
  const c = rep.collection;
  if (!c) return ' · <span class="collected none">no collection record</span>';
  const when = clock(c.ranAt);
  return (
    ' · <span class="collected">' +
    (c.producerRun ? "skjs ran" : "producer not run") +
    (when ? " at " + esc(when) : "") +
    "</span>"
  );
}

function stampFor(f, rep) {
  if (
    f.status === "not-established" &&
    f.collection === "complete" &&
    !INCOMPLETE_INPUT.has(f.result?.location?.kind)
  )
    return (
      '<span class="attention" title="SKJS accepted this function and proof search did not establish it. That is either an unsound acceptance or a limit of these rules; it is not a disproof." aria-hidden="true">⚠</span>'
    );
  if (f.status !== "verified") return '<i class="dot"></i>';
  const fresh = rep.collection?.verified === true;
  return (
    '<span class="stamp' +
    (fresh ? "" : " recorded") +
    '" title="' +
    (fresh
      ? "A certificate for this function's modeled obligations was checked by the independent consumer for this report."
      : "Recorded in the report as verified. No consumer run backs what you are looking at.") +
    '" aria-hidden="true">✓</span>'
  );
}

// What each side said about this function, spelled out rather than encoded in a
// colour: the producer's own outcome, then what proof search found. They are
// different questions, so both are shown even when they agree.
//
// The producer really does reject; the verifier never disproves. "?" therefore
// means no proof was found, not that the claim is false.
const PRODUCER_MARK = {
  complete: ["✓", "SKJS finished checking this function"],
  aborted: ["✗", "SKJS stopped inside this function"],
};
// The same outcomes in words, for the tally and the panels.
const PROOF_LABEL = {
  verified: "verified",
  "not-established": "proof search failed",
  unsupported: "unsupported source",
  "not-run": "not run",
  stale: "stale after an edit",
};
const proofLabel = (status) => PROOF_LABEL[status] || status;
// ✓ proved, ✗ searched and failed, ? could not properly try. The last covers a
// claim the extractor needed and did not find — typically because the producer
// stopped before annotating everywhere — and source outside the fragment.
// ✗ still means no proof was found, never that the claim is false.
const INCOMPLETE_INPUT = new Set([
  "missing-expression-claim",
  "missing-environment-claim",
  "source-limitation",
]);
function proofMark(f) {
  if (f.status === "verified") return ["✓", "a certificate was checked"];
  if (f.status === "unsupported")
    return ["?", "the source fragment gate rejected this file, so nothing was checked"];
  if (f.status === "not-established")
    return INCOMPLETE_INPUT.has(f.result?.location?.kind)
      ? [
          "?",
          "checking could not proceed: a claim it needed is missing, or the source is outside the fragment",
        ]
      : ["✗", "proof search failed; that is not a disproof of the claim"];
  if (f.status === "stale")
    return ["·", "stale: the candidate changed after this result"];
  return ["·", "verification was not requested"];
}

function outcomePair(f, rep) {
  const producer = PRODUCER_MARK[f.collection] || ["·", "no producer outcome recorded"];
  const proof = proofMark(f);
  // The two tools disagree when one concluded something the other did not.
  // Nothing is claimed either way when proof search never reached a verdict.
  const concluded = !INCOMPLETE_INPUT.has(f.result?.location?.kind);
  const disagrees =
    concluded &&
    ((f.collection === "complete" && f.status === "not-established") ||
      (f.collection === "aborted" && f.status === "verified"));
  return (
    '<span class="pair' +
    (disagrees ? " warn" : "") +
    '" title="' +
    esc(
      // SKJS reads only the source, so its outcome holds for as long as the
      // source does. Proof search reads the claims, so an edit can change it.
      "SKJS: " +
        producer[1] +
        ". This depends on the source file only, which is unchanged. Proof: " +
        proof[1] +
        ". This depends on the claims.",
    ) +
    '" aria-label="' +
    esc("SKJS " + producer[1] + "; proof " + proof[1]) +
    '">SKJS ' +
    producer[0] +
    " · proof " +
    proof[0] +
    "</span>"
  );
}

function renderShell() {
  const rep = state.report;
  el("srcline").innerHTML =
    "<b>" + esc(rep.file) + "</b> · producer " + esc(rep.producer) + collectedLine(rep);
  // What the report records, at a glance. Each count moves to the next function
  // it describes: with many functions, finding the unfinished ones is the first
  // thing a reader wants. Counts summarize recorded outcomes, not evidence.
  const tally = summarize(rep.functions);
  el("tally").innerHTML =
    "<span>" +
    tally.functions +
    (tally.functions === 1 ? " function" : " functions") +
    "</span>" +
    Object.entries(tally.status)
      .map(
        ([status, n]) =>
          '<button class="tallybtn ' +
          statusClass(status) +
          '" data-status="' +
          esc(status) +
          '">' +
          n +
          " " +
          esc(proofLabel(status)) +
          "</button>",
      )
      .join("") +
    (tally.gaps
      ? '<button class="tallybtn st-attn" data-gaps="1">' +
        tally.gaps +
        (tally.gaps === 1 ? " gap" : " gaps") +
        "</button>"
      : "");
  el("tally")
    .querySelectorAll("[data-status],[data-gaps]")
    .forEach((b) =>
      b.addEventListener("click", () =>
        jumpToFunction(
          b.dataset.gaps
            ? (f) => f.gaps.length > 0
            : (f) => f.status === b.dataset.status,
        ),
      ),
    );
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
        stampFor(f, rep) +
        '<span class="nm">' +
        esc(f.name) +
        "</span>" +
        outcomePair(f, rep) +
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
        state.selectedId = null;
        el("detail").innerHTML =
          '<div class="empty">Select a claim in the source to see its span and the raw producer encoding.</div>';
        renderShell();
        renderCode();
        renderFlow();
        syncLocation();
      }),
    );
  filterFunctions();
  const f = rep.functions[state.fn];
  const collected = rep.collection;
  let p =
    '<dl class="kv"><dt>collection</dt><dd>' +
    (collected
      ? esc(
          (collected.producerRun
            ? "skjs ran for this report"
            : "the producer did not run; these are candidate claims, and SKJS's own outcome still holds for this unchanged source") +
            (collected.ranAt ? " at " + clock(collected.ranAt) : "") +
            (typeof collected.durationMs === "number"
              ? " in " + (collected.durationMs / 1000).toFixed(1) + " s"
              : ""),
        ) +
        "</dd><dt>verification</dt><dd>" +
        (collected.verified
          ? "the independent consumer was run"
          : "not requested for this collection")
      : "this report was read from a file; it records no collection run") +
    "</dd></dl>";
  // The producer's own output, kept where the rest of "what produced this" is.
  // Most of it is drawn inline; this says what the source view is not showing.
  if (rep.diagnostics && rep.diagnostics.trim()) {
    const marks = producerMarks(rep);
    const inFunction = marks.filter(
      (m) => m.pos[0] >= (f?.start ?? 0) && m.pos[1] <= (f?.end ?? rep.source.length),
    ).length;
    const shown = state.producerErrors ? inFunction : 0;
    const hidden = marks.length - shown;
    p +=
      "<details><summary>Producer diagnostics (" +
      marks.length +
      ")</summary>" +
      (hidden
        ? '<div class="note">' +
          (hidden === 1 ? "One is" : hidden + " are") +
          " not drawn in the source view: " +
          (state.producerErrors
            ? hidden === 1
              ? "it belongs to another function in this file."
              : "they belong to other functions in this file."
            : "switch on SKJS errors to see the ones in this function.") +
          "</div>"
        : "") +
      '<pre class="raw">' +
      esc(rep.diagnostics) +
      "</pre></details>";
  }
  if (collected?.command)
    p +=
      '<details><summary>Producer command</summary><pre class="raw">' +
      esc(collected.command) +
      "</pre></details>";
  p +=
    '<div class="status-line ' +
    statusClass(f ? f.status : "") +
    '">' +
    (f ? stampFor(f, rep) : '<i class="dot"></i>') +
    " verification <b>" +
    esc(f ? proofLabel(f.status) : "—") +
    "</b> (recorded result)</div>" +
    (f ? '<div class="status-line">' + outcomePair(f, rep) + "</div>" : "");
  if (f?.signature)
    p +=
      '<details><summary>Producer function signature</summary><pre class="raw">' +
      esc(f.signature) +
      "</pre></details>";
  if (f && f.detail)
    p += '<div class="status-line">' + esc(f.detail) + "</div>";
  if (f?.result)
    p +=
      "<details><summary>Recorded result record</summary><pre class=\"raw\">" +
      esc(JSON.stringify(f.result, null, 2)) +
      "</pre></details>";
  if (f && f.collection)
    p +=
      '<dl class="kv"><dt>producer snapshot</dt><dd>' +
      esc(
        (f.collection === "complete"
          ? "complete"
          : "partial — the producer stopped collecting for this function") +
          (f.quality ? " · " + f.quality : "") +
          (f.mode ? " · " + f.mode : ""),
      ) +
      (collected && collected.producerRun === false
        ? "<br>This describes the original collection, not the edited candidate on screen."
        : "") +
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
async function load(text, keepCandidate = false) {
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
    el("detail").innerHTML =
      '<div class="empty">Select a claim in the source to see its span and the raw producer encoding.</div>';
    renderShell();
    renderCode();
    renderFlow();
    renderCandidateStatus();
    applyPendingMark();
  } catch (err) {
    if (version !== loadVersion) return;
    state.report = null;
    el("candidate-panel").hidden = true;
    for (const id of ["fnstrip", "flow", "detail", "prov"])
      el(id).replaceChildren();
    el("code").innerHTML =
      '<div class="empty">Could not read that file: ' +
      esc(err.message) +
      ". Expected an annotated .ts written by annotate-source.js.</div>";
  }
}

/* ---------- controls ---------- */
function setDensity(d, persist = true) {
  state.density = d;
  if (persist) store.set("density", d);
  el("d-key").setAttribute("aria-pressed", String(d === "key"));
  el("d-all").setAttribute("aria-pressed", String(d === "all"));
  if (state.report) renderCode();
}
el("d-key").addEventListener("click", () => setDensity("key"));
el("d-all").addEventListener("click", () => setDensity("all"));
el("t-err").checked = state.producerErrors;
el("t-err").addEventListener("change", (e) => {
  state.producerErrors = e.target.checked;
  store.set("errs", state.producerErrors);
  if (state.report) {
    renderCode();
    renderShell();
  }
});
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
    state.pendingMark = "";
    activeRequest++;
    document.body.classList.remove("busy");
    return load(t);
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
      state.pendingMark = "";
      activeRequest++;
      document.body.classList.remove("busy");
      return load(t);
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
    const { files, groups = [{ label: "Current verifier examples", files }] } =
      await r.json();
    if (!files.length) return;
    const sel = el("livefile");
    sel.innerHTML =
      '<option value="">Open source…</option>' +
      groups
        .map(
          (group) =>
            '<optgroup label="' +
            esc(group.label) +
            '">' +
            group.files
              .map(
                (f) =>
                  '<option value="' +
                  esc(f) +
                  '">' +
                  esc(f.split("/").pop()) +
                  "</option>",
              )
              .join("") +
            "</optgroup>",
        )
        .join("");
    el("livewrap").hidden = false;
    // The picker lists examples; any repository source can be opened by path.
    const offerFile = (file) => {
      if (![...sel.options].some((o) => o.value === file)) {
        const option = document.createElement("option");
        option.value = file;
        option.textContent = file;
        sel.append(option);
      }
      sel.value = file;
    };
    const wanted = new URLSearchParams(location.search).get("file");
    if (wanted) offerFile(wanted);
    // Verification is not optional: the server runs it whenever a verifier is
    // present, so there is nothing here to switch on.
    if (!info.verifier)
      el("srcline").insertAdjacentHTML(
        "beforeend",
        ' · <span class="collected none">no verifier built; claims only</span>',
      );
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
        const q = "api/analyse?path=" + encodeURIComponent(file);
        const res = await fetch(q, { cache: "no-store" });
        const data = await res.json();
        if (request !== activeRequest) return;
        if (data.error) throw new Error(data.error.split("\n")[0]);
        await load(data);
        syncLocation();
      } catch (err) {
        if (request !== activeRequest) return;
        state.report = null;
        for (const id of ["fnstrip", "flow", "detail", "prov"])
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
    sel.addEventListener("change", () => {
      state.pendingMark = "";
      run();
    });
    const pathInput = el("livepath"),
      pathList = el("pathlist");
    el("pathwrap").hidden = false;
    let suggesting;
    const suggest = async () => {
      try {
        const found = await fetch(
          "api/sources?q=" + encodeURIComponent(pathInput.value.trim()),
          { cache: "no-store" },
        );
        if (!found.ok) return;
        const { files: matches, total } = await found.json();
        pathList.innerHTML = matches
          .map((f) => '<option value="' + esc(f) + '"></option>')
          .join("");
        pathInput.title =
          total > matches.length
            ? total + " matching sources; showing the first " + matches.length
            : total + " matching sources";
      } catch (e) {
        /* listing is a convenience; typing a full path still works */
      }
    };
    pathInput.addEventListener("input", () => {
      clearTimeout(suggesting);
      suggesting = setTimeout(suggest, 150);
    });
    pathInput.addEventListener("change", () => {
      const file = pathInput.value.trim();
      if (!file) return;
      state.pendingMark = "";
      offerFile(file);
      run();
    });
    suggest();

    if (!wanted) sel.value = files[0];
    if (sel.value) run();
  } catch (e) {
    /* not served locally: loading a report file is still available */
  }
}
connectLive();

setDensity(state.density);

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
// Claim spans start at the declaration, but a comment written directly above a
// function belongs to it for whoever is reading. Show that block, stopping at a
// blank line or at anything that is not a comment, so a neighbour's trailing
// comment is never attributed here.
const COMMENT_LINE = /^\s*(\/\/|\/\*|\*)/;
function commentStartLine(source, starts, from, floor) {
  const lineText = (n) =>
    source.slice(starts[n], n + 1 < starts.length ? starts[n + 1] - 1 : source.length);
  let line = lineAt(starts, from);
  while (line > 0 && starts[line - 1] >= floor) {
    const text = lineText(line - 1);
    if (!text.trim() || !COMMENT_LINE.test(text)) break;
    line--;
  }
  return line;
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
