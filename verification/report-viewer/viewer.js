"use strict";
/* The page: selection, rendering and the live companion.
 *
 * These files are plain scripts sharing one global scope, loaded in order:
 * model.js (read and validate reports) → marks.js (decide what the source view
 * shows) → candidate.js (pure claim edits) → editor.js (the editing workspace)
 * → viewer.js. This file provides `state`, `el`, `load`, `select`, `renderShell`
 * and `renderCode` to editor.js, and uses `candidateState`, `renderEditor`,
 * `renderMissingEditor`, `renderCandidateStatus`, `canReplaceCandidate` and
 * `initializeCandidateEditor` from it. Nothing below decides what a mark means:
 * that lives in marks.js, where it can be tested without a browser.
 */
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
function renderCode() {
  const rep = state.report,
    f = rep.functions[state.fn];
  const starts = lineStarts(rep.source);
  const { entries: entryItems, items } = sourceMarks(rep, f, {
    density: state.density,
    unsupported: state.unsupported,
    producerErrors: state.producerErrors,
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
    ln <= lineAt(starts, Math.max(0, (f.end ?? rep.source.length) - 1));
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
  if (!warning.hidden) renderWarning(warning, f);
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
// One banner for the located failure, in the same words as the mark it points at.
function renderWarning(warning, f) {
  const failure = firstFailure(f);
  const missingClaim =
    failure?.kind === "missing-expression-claim" ||
    failure?.kind === "missing-environment-claim";
  warning.textContent =
    failure?.kind === "source-limitation"
      ? "⚠ Verification unavailable: the marked source expression is outside the supported fragment. This is not a verdict on your edited claim."
      : failure?.kind === "unavailable-type-claim"
        ? "⚠ A type this needed was never exported, so checking stopped before any proof obligation. That is not a failed proof."
      : missingClaim
        ? "⚠ Verification needs a claim this report does not contain. The marked place is where extraction stopped, not a claim that was disproved."
        : failure
          ? "⚠ Proof search failed at the marked obligation. Other claims are not individually classified."
          : "⚠ Proof search failed for this function. No claim location is available for this diagnostic.";
  if (failure) {
    const jump = document.createElement("button");
    jump.textContent =
      failure.kind === "source-limitation"
        ? "Show unsupported expression"
        : failure.kind === "unavailable-type-claim"
          ? "Show the unavailable claim"
        : missingClaim
          ? "Show the missing claim"
          : "Show failed obligation";
    jump.addEventListener("click", () => {
      select(failure.id);
      el("code")
        .querySelector('[data-id="' + failure.id + '"]')
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
      (it.mark ? ' <b class="pm">' + esc(it.mark) + "</b>" : "") +
      (it.tag ? ' <span class="tag">' + esc(it.tag) + "</span>" : "") +
      "</span>";
    cur = it.col + markWidth(it) - 1;
  }
  return out;
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

// With no claim selected, the panel offers what can be added to this function:
// its contract when it has no candidate at all, otherwise its attachment sites.
function showFunctionWorkspace() {
  el("detail").replaceChildren();
  const f = state.report?.functions[state.fn];
  if (f) renderMissingEditor(f);
  if (!el("detail").children.length)
    el("detail").innerHTML =
      '<div class="empty">Select a claim in the source to see its span and the raw producer encoding.</div>';
}

function clearSelection() {
  state.selected = null;
  state.selectedId = null;
  showFunctionWorkspace();
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
  showFunctionWorkspace();
  renderShell();
  renderCode();
  syncLocation();
}

document.addEventListener("keydown", (ev) => {
  if (!state.report) return;
  // Selecting a claim puts the cursor in its editor, so stepping between claims
  // needs a key the editor will not take: Option (Alt) with the arrows, or with
  // j and k, works while typing and leaves the next claim ready to type into.
  // The letters are matched by physical key, because Option composes characters
  // on macOS and would otherwise arrive as ∆ and ˚.
  if (ev.altKey && !ev.metaKey && !ev.ctrlKey) {
    const step =
      ev.key === "ArrowDown" || ev.code === "KeyJ"
        ? 1
        : ev.key === "ArrowUp" || ev.code === "KeyK"
          ? -1
          : 0;
    if (step) {
      ev.preventDefault();
      moveSelection(step);
    }
    return;
  }
  if (ev.metaKey || ev.ctrlKey || ev.altKey) return;
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
        : id[0] === "m"
          ? { ...f.missingSites[idx], missing: true }
          : id[0] === "u"
            ? { ...f.failureSites[idx], unclaimed: true }
            : { kind: "environment", ...f.entries[idx] };
  state.selected = item;
  el("inspector").scrollIntoView({ block: "nearest" });
  const src = state.report.source;
  let h = "";
  if (f.status === "not-established" && item.failure)
    h += failureHtml(f, item);
  // An obligation at a place with no claim. There is no record to show and
  // nothing to supply: what failed is the annotation, not a claim about it.
  if (item.unclaimed) {
    h += failureHtml(f, item);
    h +=
      '<pre class="raw">' + esc(src.slice(item.pos[0], item.pos[1])) + "</pre>";
    el("detail").innerHTML = h;
    document
      .querySelectorAll(".lab")
      .forEach((x) => x.classList.toggle("on", x.dataset.id === id));
    return;
  }
  // A missing site is a place with no claim, so there is no record to show:
  // the panel is the form for supplying one.
  if (item.missing) {
    h += '<div class="status-line"><b>No ' + esc(item.kind) + " claim here</b></div>";
    h +=
      '<pre class="raw">' + esc(src.slice(item.pos[0], item.pos[1])) + "</pre>";
    h +=
      '<div class="note">This is a source attachment site, not necessarily a ' +
      "required proof obligation. Nothing here says a claim is wrong; there is none.</div>";
    el("detail").innerHTML = h;
    renderMissingEditor(f, item.pos);
    document
      .querySelectorAll(".lab")
      .forEach((x) => x.classList.toggle("on", x.dataset.id === id));
    return;
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
    // The environment this expression is checked against. It is selectable from
    // here whether or not it is drawn: Compact hides an entry where nothing
    // changed, and that is exactly the entry a repair often has to carry — a
    // return contract fails on the value returned, while the fact it needs
    // belongs to the environment that value was read in.
    //
    // Where the obligation record names that entry, take its word for it rather
    // than inferring one from spans.
    const named =
      item.failure &&
      obligationReader.obligationView(f.obligation, state.report.source)
        ?.environmentStart;
    const entryIndex =
      (named !== null && named !== undefined
        ? f.entries
            .map((e, i) => ({ e, i }))
            .find(({ e }) => e.pos && e.pos[0] === named)
        : null) ||
      f.entries
        .map((e, i) => ({ e, i }))
        .filter(
          ({ e }) => e.pos && e.pos[0] <= item.pos[0] && e.pos[1] >= item.pos[1],
        )
        .sort((a, b) => a.e.pos[1] - a.e.pos[0] - (b.e.pos[1] - b.e.pos[0]))[0];
    if (entryIndex)
      h +=
        '<details open><summary>Containing statement entry claims</summary><pre class="raw">' +
        esc(
          entryIndex.e.bindings
            .filter((b) => state.unsupported || !isNoise(b))
            .map((b) => b.name + ": " + b.type)
            .join("\n"),
        ) +
        '</pre><button data-entry="' +
        entryIndex.i +
        '">Select this environment</button></details>';
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
    .querySelectorAll("[data-entry]")
    .forEach((b) =>
      b.addEventListener("click", () => select("n" + b.dataset.entry)),
    );
  el("detail")
    .querySelectorAll("[data-endpoint]")
    .forEach((b) =>
      b.addEventListener("click", () => {
        const [from, to] = b.dataset.endpoint.split(",").map(Number);
        const expr = f.exprs.findIndex(
          (e) => e.pos && e.pos[0] === from && e.pos[1] === to,
        );
        const entry = f.entries.findIndex((e) => e.pos && e.pos[0] === from);
        if (expr >= 0) select("e" + expr);
        else if (entry >= 0) select("n" + entry);
        revealSelected();
      }),
    );
  el("detail")
    .querySelectorAll("[data-nested]")
    .forEach((b) =>
      b.addEventListener("click", () => select(b.dataset.nested)),
    );
  document
    .querySelectorAll(".lab")
    .forEach((x) => x.classList.toggle("on", x.dataset.id === id));
}

// What happened, why, and then the obligation itself. The verifier's own
// sentence and the epistemic caveat are kept, one disclosure down: they are the
// same for every failure, and repeating them above the table buries it.
const FAILURE_TITLE = {
  "source-limitation": "Unsupported source expression",
  "missing-expression-claim": "Verification needed a claim here",
  "missing-environment-claim": "Verification needed a claim here",
  "unavailable-type-claim": "Required type unavailable",
};
// Used when no structured record was emitted: the reason has to come from the
// failure kind alone.
const FAILURE_REASON = {
  "source-limitation":
    "Source conversion stopped at this unsupported expression, before checking any proof obligation.",
  "missing-expression-claim":
    "Extraction needed a claimed type for this expression and the report has none.",
  "missing-environment-claim":
    "Extraction needed the environment claimed at this statement and the report has none.",
  "unavailable-type-claim":
    "The producer's type here is outside what the claim format can express, so it exported none and no proof obligation was reached. That is a limit of the format, not a statement about the program.",
  "edge-obligation":
    "An incoming edge did not justify the environment used at this expression.",
  "environment-obligation": "The verifier could not use this statement environment.",
};
// Claims the producer never decoded cannot be used, whatever else is wrong here.
// Naming them is a fact from this report, not a diagnosis of the failure.
function undecodedIn(item) {
  return item.kind === "environment" && Array.isArray(item.bindings)
    ? item.bindings.filter((b) => b.unavailable).map((b) => b.name)
    : [];
}

function failureHtml(f, item) {
  const view = obligationReader.obligationView(f.obligation, state.report.source);
  // Only a record says which phase stopped. Without one, saying "proof search"
  // would name a phase this reader does not know: extraction and claim decoding
  // fail here too, before any search.
  const title =
    FAILURE_TITLE[item.failureKind] ||
    (view?.phase === "proof-search"
      ? "Proof search failed here"
      : "Checking stopped here");
  const undecoded = undecodedIn(item);
  const reason =
    (view && view.what) ||
    (item.failureKind === "unavailable-type-claim" && item.failureBinding
      ? "The producer's type for ‘" +
        item.failureBinding +
        "’ here is outside what the claim format can express, so it exported " +
        "none and extraction stopped before any proof obligation. That is a " +
        "limit of the format, not a statement about the program."
      : item.failureKind === "missing-environment-claim" && item.failureBinding
      ? "The environment claimed at this statement does not include the binding ‘" +
        item.failureBinding +
        "’, which extraction needed."
      : // Without a structured record the verifier's own sentence is the most
        // specific thing there is, so it is the reason rather than a footnote.
        FAILURE_REASON[item.failureKind] ||
        (item.failure || "").replace(/^reject: /, "")) ||
    "This is where checking stopped.";
  return (
    '<div class="failure-note"><div class="status-line"><b>' +
    esc(title) +
    "</b>" +
    (view && view.role && view.title !== "Obligation at this point"
      ? ' <span class="tag">' + esc(view.title.toLowerCase()) + "</span>"
      : "") +
    "</div><p>" +
    esc(reason) +
    "</p>" +
    (undecoded.length
      ? '<div class="note">This environment carries no usable type for <b>' +
        undecoded.map(esc).join("</b>, <b>") +
        "</b>: the producer had one, and it was outside what the claim format " +
        "expresses. Nothing here can be checked until a claim is supplied.</div>"
      : "") +
    (view ? obligationHtml(view) : "") +
    '<details class="disc"><summary>record</summary><pre class="raw">' +
    esc(item.failure) +
    "</pre>" +
    (item.failureStage
      ? '<dl class="kv"><dt>stage</dt><dd>' + esc(item.failureStage) + "</dd></dl>"
      : "") +
    (view
      ? '<dl class="kv">' +
        (view.term ? "<dt>term</dt><dd>" + esc(view.term) + "</dd>" : "") +
        (view.id ? "<dt>id</dt><dd>" + esc(view.id) + "</dd>" : "") +
        "<dt>phase</dt><dd>" +
        esc(view.phase || "—") +
        "</dd><dt>search depth</dt><dd>" +
        esc(String(view.fuel ?? "—")) +
        "</dd></dl>"
      : "") +
    '<div class="note">This is the first failure reported, and explanatory ' +
    "metadata about one unsuccessful attempt. It does not prove the claim false. " +
    "Ids are local to this attempt and do not survive an edit.</div>" +
    "</details></div>"
  );
}

// The obligation as a table: what was available, what had to follow.
function obligationHtml(view) {
  if (!view) return "";
  // The rail is narrow, so the slot's note rides under its name and the types
  // keep their own line: a type broken across lines is harder to read than one
  // that scrolls.
  const slotCell = (row) =>
    "<td>" +
    esc(row.binding || "slot " + row.slot) +
    (row.note ? '<div class="slotnote">' + esc(row.note) + "</div>" : "") +
    "</td>";
  const rows = view.rows
    .map((row) =>
      view.kind === "edge-coverage"
        ? '<tr class="' +
          (row.differs ? "differs" : "") +
          '">' +
          slotCell(row) +
          "<td>" +
          esc(row.have) +
          "</td><td>" +
          esc(row.need) +
          "</td></tr>"
        : "<tr>" + slotCell(row) + "<td>" + esc(row.have) + "</td></tr>",
    )
    .join("");
  const head =
    view.kind === "edge-coverage"
      ? "<tr><th>binding</th><th>carried here</th><th>required there</th></tr>"
      : "<tr><th>binding</th><th>available</th></tr>";
  // Current-content facts sit in their own table: a slot's contract and what it
  // holds right now are different statements, and the contracts can agree while
  // these do not. Highlighted only when they are the remaining difference.
  const knowledge = view.knowledge?.length
    ? '<div class="slotwrap"><table class="slots">' +
      "<tr><th>binding</th><th>" +
      (view.kind === "edge-coverage"
        ? "current contents required there"
        : "current contents required here") +
      "</th></tr>" +
      view.knowledge
        .map(
          (row) =>
            '<tr class="' +
            (view.knowledgeIsTheDifference ? "differs" : "") +
            '"><td>' +
            esc(row.binding || "slot " + row.slot) +
            "</td><td>" +
            esc(row.what) +
            "</td></tr>",
        )
        .join("") +
      "</table></div>"
    : "";
  return (
    '<div class="obligation">' +
    '<div class="slotwrap"><table class="slots">' +
    head +
    rows +
    "</table></div>" +
    knowledge +
    (view.conclusion
      ? '<dl class="kv"><dt>must establish</dt><dd>' +
        esc(view.conclusion) +
        "</dd>" +
        // Only worth a line when it is not the conclusion already shown.
        (view.requiredResult && view.requiredResult !== view.conclusion
          ? "<dt>function result</dt><dd>" + esc(view.requiredResult) + "</dd>"
          : "") +
        "</dl>"
      : "") +
    (view.observation ? '<div class="note">' + esc(view.observation) + "</div>" : "") +
    (view.note ? '<div class="note">' + esc(view.note) + "</div>" : "") +
    endpointsHtml(view) +
    "</div>"
  );
}

// Both ends of an edge, selectable when the report actually holds a claim there.
function endpointsHtml(view) {
  const ends = view.endpoints.filter((e) => e.sourceMap?.pos);
  if (!ends.length) return "";
  return (
    '<div class="ends">' +
    ends
      .map(
        (e) =>
          '<button data-endpoint="' +
          e.sourceMap.pos.join(",") +
          '">' +
          (e.end === "from" ? "from " : "to ") +
          esc(
            state.report.source.slice(e.sourceMap.pos[0], e.sourceMap.pos[1]).trim() ||
              "point " + e.label,
          ) +
          "</button>",
      )
      .join("") +
    "</div>"
  );
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
  const { stamp, attention } = outcome(f, rep);
  if (attention)
    return '<span class="attention" title="SKJS accepted this function and proof search did not establish it. That is either an unsound acceptance or a limit of these rules; it is not a disproof." aria-hidden="true">⚠</span>';
  if (!stamp) return '<i class="dot"></i>';
  return (
    '<span class="stamp' +
    (stamp === "fresh" ? "" : " recorded") +
    '" title="' +
    (stamp === "fresh"
      ? "A certificate for this function's modeled obligations was checked by the independent consumer for this report."
      : "Recorded in the report as verified. No consumer run backs what you are looking at.") +
    '" aria-hidden="true">✓</span>'
  );
}

function outcomePair(f, rep) {
  const { producer, proof, disagrees } = outcome(f, rep);
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
    // Grouped by what actually happened rather than by recorded status: a
    // function whose required type was never exported did not fail a search.
    [
      ...rep.functions
        .reduce((groups, f) => {
          const { key, label } = outcomeGroup(f);
          groups.set(key, { key, label, count: (groups.get(key)?.count || 0) + 1 });
          return groups;
        }, new Map())
        .values(),
    ]
      .map(
        (group) =>
          '<button class="tallybtn ' +
          (group.key === "✓"
            ? "st-ok"
            : group.key === "·"
              ? "st-none"
              : "st-attn") +
          '" data-outcome="' +
          esc(group.key) +
          '">' +
          group.count +
          " " +
          esc(group.label) +
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
    .querySelectorAll("[data-outcome],[data-gaps]")
    .forEach((b) =>
      b.addEventListener("click", () =>
        jumpToFunction(
          b.dataset.gaps
            ? (f) => f.gaps.length > 0
            : (f) => outcomeGroup(f).key === b.dataset.outcome,
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
        showFunctionWorkspace();
        renderShell();
        renderCode();
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
          : "no verifier was available when this ran")
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
    '<details class="disc"><summary>how to read the marks</summary><div class="detail" style="padding:8px 0 0">' +
    "<div>Each function shows <b>SKJS ✓ · proof ✓</b>: what the producer found, then what proof search found.</div>" +
    "<div>SKJS: <b>✓</b> it finished this function, <b>✗</b> it stopped inside it. This depends on the source alone.</div>" +
    "<div>Proof: <b>✓</b> a certificate was checked, <b>✗</b> search failed, <b>?</b> it could not properly try, <b>·</b> nothing ran. This depends on the claims.</div>" +
    "<div><b>✗</b> never means a claim was disproved.</div>" +
    "<div>Amber marks a disagreement: SKJS accepted what nothing could prove (⚠), or rejected what a certificate covers.</div>" +
    "<div>A stamp marks a verified function; it is dashed when the status was only read from a file.</div>" +
    "<div>Results cover modeled obligations, not every exported claim.</div></div></details>";
  el("prov").innerHTML = p;
}

let loadVersion = 0;
// `asked` says the caller already put the question about unsaved edits, so it is
// not put twice for one action.
async function load(text, { keepCandidate = false, opening = "", asked = false } = {}) {
  if (!keepCandidate && !asked && !canReplaceCandidate(opening)) return;
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
      // A different report is a different question; what was announced about
      // the last one says nothing about this one.
      candidateState.announced.clear();
      el("verified-requester").hidden = true;
    }
    candidateState.bundle = typeof input === "object" ? input : null;
    state.report = rep;
    if (input.draftUnrendered)
      for (const f of rep.functions) {
        f.status = "stale";
        f.detail =
          "This report was saved with an edit that had not been checked. Apply an edit to check the candidate again.";
      }
    state.fn = 0;
    state.selected = null;
    state.selectedId = null;
    el("fnsearch").value = "";
    renderShell();
    renderCode();
    renderCandidateStatus();
    showFunctionWorkspace();
    applyPendingMark();
  } catch (err) {
    if (version !== loadVersion) return;
    state.report = null;
    for (const id of ["export-candidate", "restore-candidate"])
      el(id).hidden = true;
    el("candidate-status").hidden = true;
    for (const id of ["fnstrip", "detail", "prov"])
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
    return load(t, { opening: f.name });
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
      return load(t, { opening: f.name });
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
    // Choosing the other producer re-reads the file that is open, so the two
    // reports can be put side by side without retyping the path.
    el("producerwrap").hidden = false;
    el("liveproducer").addEventListener("change", () => {
      state.pendingMark = "";
      run();
    });
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
      if (!canReplaceCandidate(file.split("/").pop())) {
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
        await load(data, { asked: true });
        syncLocation();
      } catch (err) {
        if (request !== activeRequest) return;
        state.report = null;
        for (const id of ["fnstrip", "detail", "prov"])
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

initializeCandidateEditor();
