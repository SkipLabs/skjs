"use strict";
/* The editing workspace: drafts, checking and the missing-claim forms.
 *
 * Provides `candidateState`, `renderEditor`, `renderMissingEditor`,
 * `renderCandidateStatus`, `canReplaceCandidate` and `initializeCandidateEditor`
 * to viewer.js, and uses `state`, `el`, `load`, `select`, `renderShell` and
 * `renderCode` from it, plus the pure edits in candidate.js. A candidate is an
 * untrusted input: editing never changes a source snapshot or establishes a
 * result, and every applied edit is checked before it is displayed as one.
 */
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
      "Save the report or restore the original claims before loading another. Wait for any running check to finish.";
    el("candidate-status").hidden = false;
    return false;
  }
  return true;
}
// The workspace has no panel of its own: saving and restoring sit with the other
// report-wide actions, and editing happens where the claim is selected. This
// line only speaks when there is something to say about the candidate.
function renderCandidateStatus(message) {
  const editable = Boolean(candidateState.candidate);
  for (const id of ["export-candidate", "restore-candidate"])
    el(id).hidden = !editable;
  if (!editable) {
    el("candidate-status").hidden = true;
    return;
  }
  const changed =
    JSON.stringify(candidateState.candidate) !==
    JSON.stringify(candidateState.original);
  const text = message || (changed ? "Edited candidate; the producer's original claims are kept." : "");
  el("candidate-status").textContent = text;
  el("candidate-status").hidden = !text;
  el("restore-candidate").disabled = candidateState.running || !changed;
  el("export-candidate").disabled = candidateState.running;
}
// Claims are edited in the syntax they are written in; types.js prints and reads
// them. The producer's encoding stays one disclosure away, and is the only way
// to edit something this reader cannot name. Nothing is applied until the text
// reads back into an encoding.

// Enter applies a single-line field; a textarea needs Command or Control with
// it, so a newline still works where one belongs.
function applyOnEnter(field, apply) {
  field.addEventListener("keydown", (event) => {
    if (event.key !== "Enter") return;
    if (field.tagName === "TEXTAREA" && !(event.metaKey || event.ctrlKey)) return;
    event.preventDefault();
    if (!apply.disabled) apply.click();
  });
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
  editor.open = true;
  const summary = document.createElement("summary");
  summary.textContent = "Edit this claim";
  editor.append(summary);
  const surface = surfaceTypes.printClaimValue(item.kind, current);
  const note = document.createElement("p");
  note.textContent = surface
    ? item.kind === "expression"
      ? "Write the claimed type. Applying checks it; it does not make it true."
      : "Write each binding as name: type. Applying checks the result; it does not make it true."
    : "This encoding has no surface form in this reader, so it is edited as the producer's JSON.";
  editor.append(note);

  const field = document.createElement(surface ? "input" : "textarea");
  field.setAttribute("aria-label", surface ? "Claimed type" : "Candidate claim JSON");
  if (surface) field.value = surface;
  else {
    field.rows = 10;
    field.value = JSON.stringify(current, null, 2);
  }
  const error = document.createElement("div");
  error.setAttribute("role", "status");
  error.className = "field-error";
  const apply = document.createElement("button");
  apply.textContent = "Apply candidate edit";

  // Parsed on every keystroke: an edit that does not read back cannot be applied.
  const read = () =>
    surface
      ? surfaceTypes.readClaimValue(item.kind, field.value, current)
      : JSON.parse(field.value);
  const validate = () => {
    try {
      read();
      error.textContent = "";
      apply.disabled = false;
      field.classList.remove("invalid");
      return true;
    } catch (e) {
      error.textContent = e.message;
      apply.disabled = true;
      field.classList.add("invalid");
      return false;
    }
  };
  field.addEventListener("input", validate);
  applyOnEnter(field, apply);
  editor.append(field, error);

  const before = document.createElement("details");
  const label = document.createElement("summary");
  label.textContent = "Producer encoding";
  const raw = document.createElement("pre");
  raw.className = "raw";
  raw.textContent =
    original === undefined
      ? "No original claim at this site; this claim was added manually."
      : JSON.stringify(original, null, 2);
  before.append(label, raw);
  editor.append(before);

  apply.addEventListener("click", async () => {
    try {
      if (candidateState.running)
        throw new Error("Wait for the running operation to finish");
      if (!validate()) return;
      candidateState.candidate = editClaim(candidateState.candidate, fn, item, read());
      candidateState.revision++;
      invalidateCandidate();
      await checkCandidate();
    } catch (e) {
      error.textContent = e.message;
    }
  });
  editor.append(apply);
  el("detail").append(editor);
}

function invalidateCandidate() {
  // Conservative first version: all results belong to the previous candidate.
  for (const fn of state.report.functions) {
    fn.status = "stale";
    fn.detail = "Candidate changed; this result belonged to the previous claims.";
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
    el("restore-candidate").disabled = false;
  }
}
function initializeCandidateEditor() {
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
      "Report saved, with the original claims included. Source unchanged.",
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
    // Only worth saying when the reader asked about a particular place.
    if (!region) return;
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
  applyOnEnter(textarea, apply);
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
  applyOnEnter(text, apply);
  box.append(title, note, names, text, apply, error);
  el("detail").append(box);
}
