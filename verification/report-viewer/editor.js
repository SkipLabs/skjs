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
  el("verify-candidate").disabled = candidateState.running;
  el("restore-candidate").disabled = candidateState.running;
}
function renderEditor(fn, item) {
  if (!candidateState.candidate || candidateState.running) return;
  let current, original;
  try {
    current = claimValue(candidateState.candidate, fn, item);
    original = claimValue(candidateState.original, fn, item);
  } catch {
    return;
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
  raw.textContent = JSON.stringify(original, null, 2);
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
      await checkCandidate(false);
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
async function checkCandidate(verify) {
  if (candidateState.running || !candidateState.candidate) return;
  const revision = candidateState.revision;
  const fn = state.report.functions[state.fn]?.name;
  const selected = state.selected;
  candidateState.running = true;
  renderCandidateStatus(
    verify
      ? "Verifying candidate without running SKJS…"
      : "Validating candidate attachment…",
  );
  try {
    const response = await fetch("api/candidate", {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ candidate: candidateState.candidate, verify }),
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
    await load(bundle, false, null, true);
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
      verify
        ? "Candidate check completed. See each function’s recorded result."
        : "Candidate applied. Not yet verified.",
    );
  } catch (error) {
    renderCandidateStatus(
      "Candidate retained, but the operation failed: " + error.message,
    );
  } finally {
    candidateState.running = false;
    el("verify-candidate").disabled = false;
    el("restore-candidate").disabled = false;
  }
}
function initializeCandidateEditor() {
  el("verify-candidate").addEventListener("click", () => checkCandidate(true));
  el("restore-candidate").addEventListener("click", async () => {
    candidateState.candidate = structuredClone(candidateState.original);
    candidateState.revision++;
    invalidateCandidate();
    candidateState.saved = JSON.stringify(candidateState.candidate);
    await checkCandidate(false);
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
