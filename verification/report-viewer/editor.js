"use strict";
const candidateState = {
  candidate: null,
  original: null,
  bundle: null,
  revision: 0,
  running: false,
  saved: null,
};
function canReplaceCandidate() {
  if (
    candidateState.running ||
    (candidateState.candidate &&
      JSON.stringify(candidateState.candidate) !== candidateState.saved)
  ) {
    el("candidate-status").textContent =
      "Export your edits or restore the original claims before loading another report. Wait for any running check to finish.";
    return false;
  }
  return true;
}
function renderCandidateStatus(message) {
  el("candidate-panel").hidden = !candidateState.candidate;
  if (!candidateState.candidate) return;
  const changed =
    JSON.stringify(candidateState.candidate) !==
    JSON.stringify(candidateState.original);
  el("candidate-status").textContent =
    message ||
    (changed
      ? "Manual candidate; original producer claims retained."
      : "Original claims. Select an expression or environment to edit its encoding.");
  el("add-claim").disabled = candidateState.running;
  el("restore-candidate").disabled = candidateState.running;
}
function renderEditor(fn, item) {
  if (!candidateState.candidate || candidateState.running) return;
  let current, original;
  try {
    current = claimValue(candidateState.candidate, fn, item);
  } catch {
    return;
  }
  try {
    original = claimValue(candidateState.original, fn, item);
  } catch {
    original = undefined;
  }
  const editor = document.createElement("details");
  const summary = document.createElement("summary");
  summary.textContent = "Edit candidate JSON";
  editor.append(summary);
  const note = document.createElement("p");
  note.textContent =
    "Edit the type encoding (or the entry binding array). Apply validates attachment but does not verify the claim.";
  editor.append(note);
  const textarea = document.createElement("textarea");
  textarea.rows = 10;
  textarea.setAttribute("aria-label", "Candidate claim JSON");
  textarea.value = JSON.stringify(current, null, 2);
  editor.append(textarea);
  const before = document.createElement("details");
  const label = document.createElement("summary");
  label.textContent = "Original producer claim";
  const raw = document.createElement("pre");
  raw.className = "raw";
  raw.textContent =
    original === undefined
      ? "No original claim at this site; this claim was added manually."
      : JSON.stringify(original, null, 2);
  before.append(label, raw);
  editor.append(before);
  const apply = document.createElement("button");
  apply.textContent = "Apply candidate edit";
  const error = document.createElement("div");
  error.setAttribute("role", "status");
  apply.addEventListener("click", async () => {
    try {
      if (candidateState.running)
        throw new Error("Wait for the running operation to finish");
      const next = editClaim(
        candidateState.candidate,
        fn,
        item,
        JSON.parse(textarea.value),
      );
      candidateState.candidate = next;
      candidateState.revision++;
      invalidateCandidate();
      await checkCandidate();
    } catch (e) {
      error.textContent = e.message;
    }
  });
  editor.append(apply, error);
  el("detail").append(editor);
}
function invalidateCandidate() {
  // Conservative first version: all results belong to the previous candidate.
  for (const fn of state.report.functions) {
    fn.status = "stale";
    fn.detail = "Candidate changed; reverify to establish a new result.";
  }
  if (candidateState.bundle) {
    candidateState.bundle.manifest.results = null;
    candidateState.bundle.draftUnrendered = true;
  }
  renderShell();
  renderCode();
  el("detail").textContent =
    "Candidate changed; previous verification diagnostics are stale.";
  renderCandidateStatus(
    "Candidate changed. Previous verification results are stale.",
  );
}
// Applying an edit and checking it are one step: a candidate that has not been
// checked is not worth displaying as a result.
async function checkCandidate() {
  if (candidateState.running || !candidateState.candidate) return;
  const revision = candidateState.revision;
  const fn = state.report.functions[state.fn]?.name;
  const selected = state.selected;
  candidateState.running = true;
  renderCandidateStatus("Checking the candidate, without running SKJS…");
  try {
    const response = await fetch("api/candidate", {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ candidate: candidateState.candidate }),
    });
    const bundle = await response.json();
    if (revision !== candidateState.revision) return;
    if (!response.ok || bundle.error)
      throw new Error(bundle.error || "Candidate request failed");
    // Keep original producer diagnostics available, clearly attributed to that snapshot.
    bundle.manifest.diagnostics =
      candidateState.bundle?.manifest.diagnostics || "";
    bundle.originalDiagnostics = true;
    bundle.originalCandidate = candidateState.original;
    await load(bundle, true);
    const index = state.report.functions.findIndex((f) => f.name === fn);
    if (index >= 0) state.fn = index;
    renderShell();
    renderCode();
    renderFlow();
    if (selected) {
      const f = state.report.functions[state.fn];
      const expressions = selected.kind === "expression";
      const list = expressions ? f.exprs : f.entries;
      const i = list.findIndex(
        (x) => JSON.stringify(x.pos) === JSON.stringify(selected.pos),
      );
      if (i >= 0) {
        candidateState.running = false;
        select((expressions ? "e" : "n") + i);
      }
    }
    renderCandidateStatus(
      "Candidate checked. See each function’s recorded result.",
    );
    return true;
  } catch (error) {
    renderCandidateStatus(
      "Candidate retained, but the operation failed: " + error.message,
    );
    return false;
  } finally {
    candidateState.running = false;
    el("add-claim").disabled = false;
    el("restore-candidate").disabled = false;
  }
}
function initializeCandidateEditor() {
  el("add-claim").addEventListener("click", () => {
    if (!state.report) return;
    el("detail").replaceChildren();
    renderMissingEditor(state.report.functions[state.fn]);
    el("inspector").scrollIntoView({ block: "nearest" });
  });
  el("restore-candidate").addEventListener("click", async () => {
    candidateState.candidate = structuredClone(candidateState.original);
    candidateState.revision++;
    invalidateCandidate();
    candidateState.saved = JSON.stringify(candidateState.candidate);
    await checkCandidate();
  });
  el("export-candidate").addEventListener("click", () => {
    if (!candidateState.bundle || candidateState.running) return;
    // Results are display records only. A saved draft still needs a fresh check.
    const bundle = {
      ...candidateState.bundle,
      candidate: candidateState.candidate,
      originalCandidate: candidateState.original,
    };
    const url = URL.createObjectURL(
      new Blob([JSON.stringify(bundle, null, 2)], { type: "application/json" }),
    );
    const link = document.createElement("a");
    link.href = url;
    link.download = "claim-candidate.json";
    link.click();
    setTimeout(() => URL.revokeObjectURL(url), 1000);
    candidateState.saved = JSON.stringify(candidateState.candidate);
    renderCandidateStatus(
      "Candidate bundle exported; original claims included. Source unchanged.",
    );
  });
}

function renderMissingEditor(fn, region) {
  if (!candidateState.candidate || candidateState.running) return;
  if (fn.candidateMissing) {
    renderFunctionEditor(fn);
    return;
  }
  const sites = (fn.missingSites || []).filter(
    (s) => !region || (s.pos[0] >= region[0] && s.pos[1] <= region[1]),
  );
  const box = document.createElement("section");
  const title = document.createElement("h3");
  title.textContent = "Add a missing claim";
  box.append(title);
  if (!sites.length) {
    const note = document.createElement("p");
    note.textContent = "No missing attachment sites listed here.";
    box.append(note);
    el("detail").append(box);
    return;
  }
  const note = document.createElement("p");
  note.textContent =
    "These are source attachment sites, not necessarily required proof obligations. Supply a type or entry binding array; no type is inferred for you.";
  box.append(note);
  const selectSite = document.createElement("select");
  selectSite.setAttribute("aria-label", "Missing claim site");
  const source = state.report.source,
    starts = lineStarts(source);
  for (const [i, site] of sites.entries()) {
    const option = document.createElement("option");
    option.value = i;
    option.textContent = `${site.kind} · line ${lineAt(starts, site.pos[0]) + 1} · ${source
      .slice(...site.pos)
      .replace(/\s+/g, " ")
      .slice(0, 80)}`;
    selectSite.append(option);
  }
  const preview = document.createElement("pre");
  preview.className = "raw";
  const textarea = document.createElement("textarea");
  textarea.rows = 8;
  textarea.setAttribute("aria-label", "New claim JSON");
  const show = () => {
    preview.textContent = source.slice(...sites[+selectSite.value].pos);
    textarea.value = "";
    textarea.placeholder =
      sites[+selectSite.value].kind === "environment"
        ? "Array of {name, type} bindings"
        : "Type encoding in the candidate format";
  };
  selectSite.addEventListener("change", show);
  show();
  const apply = document.createElement("button");
  apply.textContent = "Add candidate claim";
  const error = document.createElement("div");
  error.setAttribute("role", "status");
  apply.addEventListener("click", async () => {
    try {
      if (candidateState.running)
        throw new Error("Wait for the running check to finish");
      const site = sites[+selectSite.value];
      candidateState.candidate = addClaim(
        candidateState.candidate,
        fn,
        site,
        JSON.parse(textarea.value),
      );
      candidateState.revision++;
      state.selected = { ...site };
      invalidateCandidate();
      await checkCandidate();
    } catch (e) {
      error.textContent = e.message;
    }
  });
  box.append(selectSite, preview, textarea, apply, error);
  el("detail").append(box);
}

function renderFunctionEditor(fn) {
  const box = document.createElement("section");
  const title = document.createElement("h3");
  title.textContent = "Add function candidate: " + fn.name;
  const note = document.createElement("p");
  note.textContent =
    "Supply a JSON contract with params (names and types in source order) and result. Types use the current candidate encoding. The verifier checks them against source annotations; none are inferred here.";
  const names = document.createElement("p");
  names.textContent = "Parameters: " + (fn.parameters.join(", ") || "none");
  const text = document.createElement("textarea");
  text.rows = 10;
  text.setAttribute("aria-label", "Function contract JSON");
  text.placeholder = '{"params": [...], "result": ...}';
  const apply = document.createElement("button");
  apply.textContent = "Add function candidate";
  const error = document.createElement("div");
  error.setAttribute("role", "status");
  apply.addEventListener("click", async () => {
    try {
      if (candidateState.running)
        throw new Error("Wait for the current operation to finish");
      candidateState.candidate = addFunction(
        candidateState.candidate,
        fn,
        JSON.parse(text.value),
      );
      candidateState.revision++;
      state.selected = null;
      invalidateCandidate();
      if (await checkCandidate())
        renderMissingEditor(state.report.functions[state.fn]);
    } catch (e) {
      error.textContent = e.message;
    }
  });
  box.append(title, note, names, text, apply, error);
  el("detail").append(box);
}
