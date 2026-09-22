import surface from "../tools/claim-text.mts";
import type { Candidate } from "./types.ts";
import type { ShownFunction, Site } from "./model.mts";
import type { Span } from "../tools/span.mts";
import type {
  SkjsEntry,
  SkjsExpression,
  SkjsNamedPoint,
} from "../tools/skjs-claims.mts";
import type {
  ClaimType,
  CurrentFields,
  EntryClaim,
  ExpressionClaim,
  Labels,
  NamedPoint,
  Point,
  Row,
} from "../tools/source-claims.mts";
import { decodeLabels } from "../tools/type-graph.mts";

/** Where a claim sits, in the terms the candidate is addressed by. */
export interface ClaimSite {
  kind: "expression" | "environment";
  pos: [number, number];
}

/** How a function is addressed in a candidate: by name, and by where its name
 * sits. Both, because a name can repeat within one file. */
type FunctionRef = Pick<ShownFunction, "name" | "namePos">;

/** How a site is addressed: what kind it is, and where. The reader hands over
 * whatever is selected, including the kinds that carry no claim at all. */
export type SiteRef = { kind: Site["kind"]; pos: Span };

/** The candidate's own value at a site, in the producer's encoding. */

// Candidates are untrusted inputs. Editing never changes a source snapshot or
// establishes a verification result. Keep producer data separate from the draft.
const isRecord = (v: unknown): v is Record<string, unknown> =>
  !!v && typeof v === "object" && !Array.isArray(v);
const isList = (v: unknown): v is unknown[] => Array.isArray(v);
const sameSpan = (a: unknown, b: unknown) =>
  JSON.stringify(a) === JSON.stringify(b);

/** Where a site's claim is stored. The two documents keep it in differently
 * named fields, and state different things: SKJS a type alone, the normalized
 * sidecar a type together with what the cell holds there. */
type Slot =
  | { at: "skjs-expression"; claim: SkjsExpression }
  | { at: "skjs-entry"; entry: SkjsEntry }
  | { at: "expression"; claim: ExpressionClaim }
  | { at: "entry"; entry: EntryClaim };

function claimSlot(candidate: Candidate, fn: FunctionRef, item: SiteRef): Slot {
  const named = (name: string, namePos: unknown) =>
    name === fn.name && sameSpan(namePos, fn.namePos);
  if (candidate.format === "skjs") {
    const file = candidate.claims.find((f) => f.file === candidate.file);
    const target = file?.functions.find((f) => named(f.name, f.namePos));
    if (!target) throw new Error("Candidate has no matching function");
    if (item.kind === "expression") {
      const claim = target.exprs.find((e) => sameSpan(e.pos, item.pos));
      if (!claim) throw new Error("Candidate has no matching expression");
      return { at: "skjs-expression", claim };
    }
    if (item.kind !== "environment")
      throw new Error("Select an expression or environment claim");
    const entry = target.envs.find((e) => e.pos[0] === item.pos[0]);
    if (!entry) throw new Error("Candidate has no matching entry");
    return { at: "skjs-entry", entry };
  }
  const target = candidate.claims.functions.find((f) =>
    named(f.name, f.namePos),
  );
  if (!target) throw new Error("Candidate has no matching function");
  if (item.kind === "expression") {
    const claim = target.expressions.find((e) => sameSpan(e.pos, item.pos));
    if (!claim) throw new Error("Candidate has no matching expression");
    return { at: "expression", claim };
  }
  if (item.kind !== "environment")
    throw new Error("Select an expression or environment claim");
  const entry = target.entries.find((e) => e.start === item.pos[0]);
  if (!entry) throw new Error("Candidate has no matching entry");
  return { at: "entry", entry };
}
// A claim is a type. Both encodings count: a normalized type is a list of graph
// labels, where the empty list is the empty union, and a producer type is the
// {top, atoms} form or the marker saying the producer could not decode one.
// Anything else is not a claim about this site at all; the verifier would reject
// it later, with a message about a place rather than about what was typed here.
const claimedType = (t: unknown): boolean =>
  isList(t)
    ? t.every(
        (label) =>
          typeof label === "number" && Number.isInteger(label) && label >= 0,
      )
    : isRecord(t) &&
      (typeof t.unavailable === "string" ||
        typeof t.param === "string" ||
        (isRecord(t.scheme) &&
          isList(t.scheme.typeParams) &&
          t.scheme.typeParams.length > 0 &&
          t.scheme.typeParams.every(
            (p) =>
              isRecord(p) &&
              typeof p.name === "string" &&
              p.name.length > 0 &&
              (p.bound === null || claimedType(p.bound)),
          ) &&
          isList(t.scheme.params) &&
          t.scheme.params.every(claimedType) &&
          claimedType(t.scheme.result)) ||
        t.unsupported === true ||
        (typeof t.top === "boolean" && isList(t.atoms)));
// There is one editor and it speaks the producer's structural encoding. A
// candidate in the normalized encoding is lowered here on the way in, interning
// into its own type table the rows the edit needs; a label list written
// directly is kept as written. Every normalized point says its current-content
// assertion, `null` for none.
const point = (
  types: unknown,
  value: unknown,
  current: CurrentFields | null = null,
): Point => {
  // A rigid parameter names the function's own binder and an unavailable type
  // names no type at all: neither has a row to intern, so both are stored as
  // the claim they already are.
  if (isRecord(value)) {
    if (typeof value.param === "string")
      return { current, type: { param: value.param } };
    if (isRecord(value.scheme))
      return { current, type: value as ClaimType };
    if (typeof value.unavailable === "string")
      return { current, type: { unavailable: value.unavailable } };
    const atoms = isList(value.atoms) ? value.atoms : [];
    const only = atoms.length === 1 ? atoms[0] : undefined;
    if (
      value.top === false &&
      Object.keys(value).length === 2 &&
      isRecord(only) &&
      only.a === "param" &&
      typeof only.name === "string" &&
      Object.keys(only).length === 2
    )
      return { current, type: { param: only.name } };
  }
  return { current, ...surface.lower(types, value) };
};
type EditableBinding = SkjsNamedPoint & { current?: CurrentFields | null };
const bindings = (types: Row[], value: EditableBinding[]): NamedPoint[] =>
  value.map((b) => ({
    name: b.name,
    ...point(
      types,
      b.type,
      b.current == null ? null : decodeCurrent(b.current, types.length),
    ),
  }));

/** A current-contents assertion names a field and the labels it may hold. An
 * object has one location per field, so an assertion carries the field it is
 * about; a claim that names none is refused rather than read as `value`. */
const decodeCurrent = (value: unknown, bound: number): CurrentFields => {
  if (!Array.isArray(value) || !value.length)
    throw Error("a current-contents assertion names at least one field");
  const names = new Set<string>();
  return value.map((entry) => {
    if (!Array.isArray(entry) || entry.length !== 2 || typeof entry[0] !== "string")
      throw Error("a current-contents assertion names a field and its labels");
    if (names.has(entry[0])) throw Error("duplicate field in a current-contents assertion");
    names.add(entry[0]);
    return [entry[0], decodeLabels(entry[1], bound)];
  });
};

/** An environment is a list of named claims, and nothing else is one. */
const isEnvironment = (value: unknown): value is EditableBinding[] =>
  isList(value) &&
  value.every(
    (b) =>
      isRecord(b) &&
      typeof b.name === "string" &&
      claimedType(b.type) &&
      (b.current === undefined ||
        b.current === null ||
        (isList(b.current) &&
          b.current.every(
            (entry) => isList(entry) && entry.length === 2 && typeof entry[0] === "string" &&
              isList(entry[1]) && entry[1].every((l) => typeof l === "number" && Number.isSafeInteger(l) && l >= 0),
          ))),
  );
const ENVIRONMENT_REQUIRED =
  "An environment must be an array of {name, type} bindings";

function claimValue(candidate: Candidate, fn: FunctionRef, item: SiteRef) {
  const slot = claimSlot(candidate, fn, item);
  switch (slot.at) {
    case "skjs-expression":
      return slot.claim.type;
    case "skjs-entry":
      return slot.entry.vars;
    case "expression":
      return slot.claim.type;
    case "entry":
      return slot.entry.bindings;
  }
}

/** The type table a normalized candidate interns into. */
const tableOf = (candidate: Candidate) =>
  candidate.format === "source-claims" ? candidate.claims.types : [];

function editClaim(
  candidate: Candidate,
  fn: FunctionRef,
  item: SiteRef,
  value: unknown,
): Candidate {
  const next = structuredClone(candidate);
  const slot = claimSlot(next, fn, item);
  if (item.kind === "environment" && !isEnvironment(value))
    throw new Error(ENVIRONMENT_REQUIRED);
  const types = tableOf(next);
  switch (slot.at) {
    case "skjs-expression":
      slot.claim.type = value;
      break;
    case "skjs-entry":
      if (isEnvironment(value)) slot.entry.vars = value;
      break;
    case "expression":
      Object.assign(slot.claim, point(types, value, slot.claim.current));
      break;
    case "entry":
      if (isEnvironment(value)) slot.entry.bindings = bindings(types, value);
      break;
  }
  return next;
}
function addClaim(
  candidate: Candidate,
  fn: ShownFunction,
  site: ClaimSite,
  value: unknown,
): Candidate {
  if (
    !fn.sites.some(
      (s) =>
        s.kind === "unclaimed" &&
        s.claims === site.kind &&
        sameSpan(s.pos, site.pos),
    )
  )
    throw new Error("Choose a missing site from this source snapshot");
  const next = structuredClone(candidate);
  const missing = "Adding claims requires an existing function candidate";
  const named = (name: string, namePos: unknown) =>
    name === fn.name && sameSpan(namePos, fn.namePos);
  if (site.kind !== "expression" && site.kind !== "environment")
    throw new Error("Unsupported claim site");
  if (next.format === "skjs") {
    const file = next.claims.find((f) => f.file === next.file);
    const target = file?.functions.find((f) => named(f.name, f.namePos));
    if (!target) throw new Error(missing);
    if (site.kind === "expression") {
      if (!claimedType(value))
        throw new Error("An expression claim must be a type");
      if (target.exprs.some((e) => sameSpan(e.pos, site.pos)))
        throw new Error("An expression claim already exists here");
      target.exprs.push({ pos: site.pos, type: value });
    } else {
      if (!isEnvironment(value)) throw new Error(ENVIRONMENT_REQUIRED);
      if (target.envs.some((e) => e.pos[0] === site.pos[0]))
        throw new Error("An entry claim already exists here");
      target.envs.push({ pos: site.pos, vars: value });
      target.envs.sort((a, b) => a.pos[0] - b.pos[0]);
    }
    return next;
  }
  const target = next.claims.functions.find((f) => named(f.name, f.namePos));
  if (!target) throw new Error(missing);
  const types = next.claims.types;
  if (site.kind === "expression") {
    if (!claimedType(value))
      throw new Error("An expression claim must be a type");
    if (target.expressions.some((e) => sameSpan(e.pos, site.pos)))
      throw new Error("An expression claim already exists here");
    target.expressions.push({ pos: site.pos, ...point(types, value) });
  } else {
    if (!isEnvironment(value)) throw new Error(ENVIRONMENT_REQUIRED);
    if (target.entries.some((e) => e.start === site.pos[0]))
      throw new Error("An entry claim already exists here");
    target.entries.push({
      start: site.pos[0],
      bindings: bindings(types, value),
    });
    // Normalized wire entries are sorted by source offset.
    target.entries.sort((a, b) => a.start - b.start);
  }
  return next;
}
function addFunction(
  candidate: Candidate,
  fn: ShownFunction,
  contract: unknown,
): Candidate {
  if (!fn.candidateMissing)
    throw new Error("Select a function without a candidate");
  const names = fn.parameters ?? [];
  const params =
    isRecord(contract) && isList(contract.params) ? contract.params : null;
  if (
    !isRecord(contract) ||
    !params ||
    !("result" in contract) ||
    params.length !== names.length ||
    params.some((p, i) => !isRecord(p) || p.name !== names[i] || !("type" in p))
  )
    throw new Error(
      "Supply params in source order, each with name and type, and a result type",
    );
  if (!isEnvironment(params))
    throw new Error("Each parameter needs a name and a type");
  const next = structuredClone(candidate);
  const header = { name: fn.name, namePos: spanOf(fn.namePos) };
  if (next.format === "skjs") {
    const file = next.claims.find((f) => f.file === next.file);
    if (!file) throw new Error("Candidate has no matching source file");
    if (file.functions.some((f) => f.namePos[0] === header.namePos[0]))
      throw new Error("Function candidate already exists");
    file.functions.push({
      ...header,
      params,
      retType: contract.result,
      envs: [],
      exprs: [],
    });
    return next;
  }
  const file = next.claims;
  if (file.functions.some((f) => f.namePos[0] === header.namePos[0]))
    throw new Error("Function candidate already exists");
  // A contract is types alone: a parameter or a result holds nothing.
  const types = file.types;
  const lowered = bindings(types, params);
  const result = point(types, contract.result);
  if (lowered.some((p) => p.current !== null) || result.current !== null)
    throw new Error("A contract cannot carry a current-content assertion");
  file.functions.push({
    ...header,
    params: lowered,
    result: result.type,
    entries: [],
    expressions: [],
  });
  return next;
}
/** A shown function always has one; a report that omitted it would be a report
 * about no declaration. */
const spanOf = (pos: [number, number] | undefined): [number, number] => {
  if (!pos) throw new Error("Select a function the source declares");
  return pos;
};
// What the editor is shown: a normalized claim lifted into the structural
// encoding the surface syntax reads and writes, or as stored where it has no
// faithful form there — an intersection of contracts, a type that refers to
// itself — which is then edited as the encoding.
function editable(candidate: Candidate, fn: FunctionRef, item: SiteRef) {
  if (candidate.format === "skjs") return claimValue(candidate, fn, item);
  const types = candidate.claims.types;
  const lifted = (labels: ClaimType, current: CurrentFields | null) => {
    const type =
      isRecord(labels)
        ? "param" in labels
          ? { top: false, atoms: [{ a: "param", name: labels.param }] }
          : labels
        : surface.lift(types, labels, current);
    return type && surface.roundTrips(type) ? type : labels;
  };
  const slot = claimSlot(candidate, fn, item);
  switch (slot.at) {
    case "expression":
      return lifted(slot.claim.type, slot.claim.current);
    case "entry":
      return slot.entry.bindings.map((b) => ({
        name: b.name,
        type: lifted(b.type, b.current),
      }));
    // The format decided which of the four this is; these two are the other
    // document's, and are what `claimValue` already returns for it.
    case "skjs-expression":
      return slot.claim.type;
    case "skjs-entry":
      return slot.entry.vars;
  }
}
export { claimValue, editable, editClaim, addClaim, addFunction };
