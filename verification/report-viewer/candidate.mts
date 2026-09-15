
import surface from "../tools/claim-text.mts";

/** Where a claim sits, in the terms the candidate is addressed by. */
export interface ClaimSite {
  kind: "expression" | "environment";
  pos: [number, number];
}

/** The candidate's own value at a site, in the producer's encoding. */

// Candidates are untrusted inputs. Editing never changes a source snapshot or
// establishes a verification result. Keep producer data separate from the draft.
function claimSlot(candidate: any, fn: any, item: any) {
  const sameSpan = (a: any, b: any) => JSON.stringify(a) === JSON.stringify(b);
  const file =
    candidate.format === "skjs"
      ? candidate.claims.find((f: any) => f.file === candidate.file)
      : candidate.claims;
  const target = file?.functions.find(
    (f: any) => f.name === fn.name && sameSpan(f.namePos, fn.namePos),
  );
  if (!target) throw new Error("Candidate has no matching function");
  if (item.kind === "expression") {
    const expressions =
      candidate.format === "skjs" ? target.exprs : target.expressions;
    const claim = expressions.find((e: any) => sameSpan(e.pos, item.pos));
    if (!claim) throw new Error("Candidate has no matching expression");
    return { object: claim, key: "type" };
  }
  if (item.kind !== "environment")
    throw new Error("Select an expression or environment claim");
  const entries = candidate.format === "skjs" ? target.envs : target.entries;
  const entry = entries.find((e: any) =>
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
const claimedType = (t: any) =>
  Array.isArray(t)
    ? t.every((label) => Number.isInteger(label) && label >= 0)
    : Boolean(t) &&
      typeof t === "object" &&
      (typeof t.unavailable === "string" || typeof t.param === "string" || t.unsupported === true ||
        (typeof t.top === "boolean" && Array.isArray(t.atoms)));
// There is one editor and it speaks the producer's structural encoding. A
// candidate in the normalized encoding is lowered here on the way in, interning
// into its own type table the rows the edit needs; a label list written
// directly is kept as written. Every normalized point says its current-content
// assertion, `null` for none.
const point = (types: any, value: any, current: any = null) => ({
  current,
  ...(value?.param || value?.unavailable ? {type:value} : value?.top === false && Object.keys(value).length === 2 && value.atoms?.length === 1 &&
    value.atoms[0].a === "param" && Object.keys(value.atoms[0]).length === 2 ?
    {type:{param:value.atoms[0].name}} : surface.lower(types, value)),
});
const bindings = (types: any, value: any[]) =>
  value.map((b) => ({ name: b.name, ...point(types, b.type, b.current) }));

function editClaim(candidate: any, fn: any, item: any, value: any) {
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
  if (next.format === "skjs") slot.object[slot.key] = value;
  else if (item.kind === "expression")
    Object.assign(slot.object, point(next.claims.types, value, slot.object.current));
  else slot.object.bindings = bindings(next.claims.types, value);
  return next;
}
function addClaim(candidate: any, fn: any, site: any, value: any) {
  const sameSpan = (a: any, b: any) => JSON.stringify(a) === JSON.stringify(b);
  if (
    !fn.sites?.some(
      (s: any) => s.kind === "unclaimed" && s.claims === site.kind && sameSpan(s.pos, site.pos),
    )
  )
    throw new Error("Choose a missing site from this source snapshot");
  const next = structuredClone(candidate);
  const file =
    next.format === "skjs"
      ? next.claims.find((f: any) => f.file === next.file)
      : next.claims;
  const target = file?.functions.find(
    (f: any) => f.name === fn.name && sameSpan(f.namePos, fn.namePos),
  );
  if (!target)
    throw new Error("Adding claims requires an existing function candidate");
  const skjs = next.format === "skjs";
  if (site.kind === "expression") {
    if (!claimedType(value))
      throw new Error("An expression claim must be a type");
    const expressions = skjs ? target.exprs : target.expressions;
    if (expressions.some((e: any) => sameSpan(e.pos, site.pos)))
      throw new Error("An expression claim already exists here");
    expressions.push(
      skjs ? { pos: site.pos, type: value } : { pos: site.pos, ...point(next.claims.types, value) },
    );
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
    if (entries.some((e: any) => (skjs ? e.pos[0] : e.start) === site.pos[0]))
      throw new Error("An entry claim already exists here");
    entries.push(
      skjs
        ? { pos: site.pos, vars: value }
        : { start: site.pos[0], bindings: bindings(next.claims.types, value) },
    );
    // Normalized wire entries are sorted by source offset.
    entries.sort(
      (a: any, b: any) => (skjs ? a.pos[0] : a.start) - (skjs ? b.pos[0] : b.start),
    );
  } else throw new Error("Unsupported claim site");
  return next;
}
function addFunction(candidate: any, fn: any, contract: any) {
  if (!fn.candidateMissing)
    throw new Error("Select a function without a candidate");
  if (
    !contract ||
    !Array.isArray(contract.params) ||
    !("result" in contract) ||
    contract.params.length !== fn.parameters.length ||
    contract.params.some(
      (p: any, i: number) => !p || p.name !== fn.parameters[i] || !("type" in p),
    )
  )
    throw new Error(
      "Supply params in source order, each with name and type, and a result type",
    );
  const next = structuredClone(candidate);
  const file =
    next.format === "skjs"
      ? next.claims.find((f: any) => f.file === next.file)
      : next.claims;
  if (!file) throw new Error("Candidate has no matching source file");
  if (file.functions.some((f: any) => f.namePos[0] === fn.namePos[0]))
    throw new Error("Function candidate already exists");
  const header = { name: fn.name, namePos: fn.namePos };
  if (next.format === "skjs") {
    file.functions.push({ ...header, params: contract.params, retType: contract.result, envs: [], exprs: [] });
    return next;
  }
  // A contract is types alone: a parameter or a result holds nothing.
  const types = next.claims.types;
  const params = bindings(types, contract.params);
  const result = point(types, contract.result);
  if (params.some((p) => p.current !== null) || result.current !== null)
    throw new Error("A contract cannot carry a current-content assertion");
  file.functions.push({ ...header, params, result: result.type, entries: [], expressions: [] });
  return next;
}
// What the editor is shown: a normalized claim lifted into the structural
// encoding the surface syntax reads and writes, or as stored where it has no
// faithful form there — an intersection of contracts, a type that refers to
// itself — which is then edited as the encoding.
function editable(candidate: any, fn: any, item: any) {
  const value = claimValue(candidate, fn, item);
  if (candidate.format === "skjs") return value;
  const types = candidate.claims.types;
  const lifted = (labels: any, current: any) => {
    const type = labels?.param ? {top:false,atoms:[{a:"param",name:labels.param}]} : surface.lift(types, labels, current);
    return type && surface.roundTrips(type) ? type : labels;
  };
  if (item.kind === "expression")
    return lifted(value, claimSlot(candidate, fn, item).object.current);
  return value.map((b: any) => ({ name: b.name, type: lifted(b.type, b.current) }));
}
function claimValue(candidate: any, fn: any, item: any) {
  const slot = claimSlot(candidate, fn, item);
  return slot.object[slot.key];
}
export { claimValue, editable, editClaim, addClaim, addFunction };