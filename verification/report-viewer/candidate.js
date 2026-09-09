"use strict";

// Candidates are untrusted inputs. Editing never changes a source snapshot or
// establishes a verification result. Keep producer data separate from the draft.
function claimSlot(candidate, fn, item) {
  const sameSpan = (a, b) => JSON.stringify(a) === JSON.stringify(b);
  const file =
    candidate.format === "skjs"
      ? candidate.claims.find((f) => f.file === candidate.file)
      : candidate.claims;
  const target = file?.functions.find(
    (f) => f.name === fn.name && sameSpan(f.namePos, fn.namePos),
  );
  if (!target) throw new Error("Candidate has no matching function");
  if (item.kind === "expression") {
    const expressions =
      candidate.format === "skjs" ? target.exprs : target.expressions;
    const claim = expressions.find((e) => sameSpan(e.pos, item.pos));
    if (!claim) throw new Error("Candidate has no matching expression");
    return { object: claim, key: "type" };
  }
  if (item.kind !== "environment")
    throw new Error("Select an expression or environment claim");
  const entries = candidate.format === "skjs" ? target.envs : target.entries;
  const entry = entries.find((e) =>
    candidate.format === "skjs"
      ? e.pos[0] === item.pos[0]
      : e.start === item.pos[0],
  );
  if (!entry) throw new Error("Candidate has no matching entry");
  return {
    object: entry,
    key: candidate.format === "skjs" ? "vars" : "bindings",
  };
}
// A claim is a type. Both encodings count: a normalized type is a list of graph
// labels, where the empty list is the empty union, and a producer type is the
// {top, atoms} form or the marker saying the producer could not decode one.
// Anything else is not a claim about this site at all; the verifier would reject
// it later, with a message about a place rather than about what was typed here.
const claimedType = (t) =>
  Array.isArray(t)
    ? t.every((label) => Number.isInteger(label) && label >= 0)
    : Boolean(t) &&
      typeof t === "object" &&
      (t.unsupported === true ||
        (typeof t.top === "boolean" && Array.isArray(t.atoms)));
function editClaim(candidate, fn, item, value) {
  const next = structuredClone(candidate);
  const slot = claimSlot(next, fn, item);
  if (
    item.kind === "environment" &&
    (!Array.isArray(value) ||
      value.some(
        (b) => !b || typeof b.name !== "string" || !claimedType(b.type),
      ))
  )
    throw new Error("An environment must be an array of {name, type} bindings");
  slot.object[slot.key] = value;
  return next;
}
function addClaim(candidate, fn, site, value) {
  const sameSpan = (a, b) => JSON.stringify(a) === JSON.stringify(b);
  if (
    !fn.missingSites?.some(
      (s) => s.kind === site.kind && sameSpan(s.pos, site.pos),
    )
  )
    throw new Error("Choose a missing site from this source snapshot");
  const next = structuredClone(candidate);
  const file =
    next.format === "skjs"
      ? next.claims.find((f) => f.file === next.file)
      : next.claims;
  const target = file?.functions.find(
    (f) => f.name === fn.name && sameSpan(f.namePos, fn.namePos),
  );
  if (!target)
    throw new Error("Adding claims requires an existing function candidate");
  const skjs = next.format === "skjs";
  if (site.kind === "expression") {
    if (!claimedType(value))
      throw new Error("An expression claim must be a type");
    const expressions = skjs ? target.exprs : target.expressions;
    if (expressions.some((e) => sameSpan(e.pos, site.pos)))
      throw new Error("An expression claim already exists here");
    expressions.push({ pos: site.pos, type: value });
  } else if (site.kind === "environment") {
    if (
      !Array.isArray(value) ||
      value.some(
        (b) => !b || typeof b.name !== "string" || !claimedType(b.type),
      )
    )
      throw new Error(
        "An environment must be an array of {name, type} bindings",
      );
    const entries = skjs ? target.envs : target.entries;
    if (entries.some((e) => (skjs ? e.pos[0] : e.start) === site.pos[0]))
      throw new Error("An entry claim already exists here");
    entries.push(
      skjs
        ? { pos: site.pos, vars: value }
        : { start: site.pos[0], bindings: value },
    );
    // Normalized wire entries are sorted by source offset.
    entries.sort(
      (a, b) => (skjs ? a.pos[0] : a.start) - (skjs ? b.pos[0] : b.start),
    );
  } else throw new Error("Unsupported claim site");
  return next;
}
function addFunction(candidate, fn, contract) {
  if (!fn.candidateMissing)
    throw new Error("Select a function without a candidate");
  if (
    !contract ||
    !Array.isArray(contract.params) ||
    !("result" in contract) ||
    contract.params.length !== fn.parameters.length ||
    contract.params.some(
      (p, i) => !p || p.name !== fn.parameters[i] || !("type" in p),
    )
  )
    throw new Error(
      "Supply params in source order, each with name and type, and a result type",
    );
  const next = structuredClone(candidate);
  const file =
    next.format === "skjs"
      ? next.claims.find((f) => f.file === next.file)
      : next.claims;
  if (!file) throw new Error("Candidate has no matching source file");
  if (file.functions.some((f) => f.namePos[0] === fn.namePos[0]))
    throw new Error("Function candidate already exists");
  const header = {
    name: fn.name,
    namePos: fn.namePos,
    params: contract.params,
  };
  file.functions.push(
    next.format === "skjs"
      ? { ...header, retType: contract.result, envs: [], exprs: [] }
      : { ...header, result: contract.result, entries: [], expressions: [] },
  );
  return next;
}
function claimValue(candidate, fn, item) {
  const slot = claimSlot(candidate, fn, item);
  return slot.object[slot.key];
}
if (typeof module !== "undefined")
  module.exports = { claimValue, editClaim, addClaim, addFunction };
