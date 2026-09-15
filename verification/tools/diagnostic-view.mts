/* Reading the verifier's diagnostic record for display.
 *
 * A record describes an unsuccessful verification attempt: the assumptions that
 * were available and the conclusion that had to follow. It is explanatory
 * metadata, never proof evidence and never a judgement that a claim is false.
 * See ../OBLIGATION-DIAGNOSTICS.md. Everything here is pure, so the tests can
 * exercise it without a browser.
 */

import surface from "./claim-type-text.mts";
import { decodeGraph, graphDefinitions, printLabels, type GraphDefinition } from "./type-graph.mts";
import type { ObligationDiagnostic } from "./diagnostic.mts";
import { printTerm } from "./calculus-language.mts";
import type { Span } from "../tools/source-claims.mts";

/** One binding of the context: what was carried, and what was required. */
export interface ContextRow {
  slot: number;
  binding: string;
  have: string;
  /** What the destination required. A node obligation requires nothing here. */
  need?: string;
  differs?: boolean;
  /**
   * What this slot is, where the role says something the name does not: the
   * value being returned, for a return contract's slot 0.
   */
  note?: string;
}

/**
 * A heap fact the obligation needed, where it needed any: the binding it is
 * about, and what is true of it, already phrased ("holds true", "is a read
 * of cell").
 */
export interface KnowledgeRow {
  slot: number;
  binding: string;
  what: string;
}

/** One end of an edge, and where in the source that end sits. */
export interface Endpoint {
  end: "from" | "to";
  label: number;
  sourceMap: {
    pos: Span | null;
    role: string;
    environmentStart?: number;
    context?: { name: string; span: Span | null }[];
  } | null;
}

/**
 * What the verifier had and what had to follow from it. Explanatory metadata
 * about an unsuccessful attempt — never evidence, and never a statement that
 * a claim is false.
 */
export interface ObligationView {
  /** Source-named explanation prepared by the report writer. */
  summary?: string;
  focus?: { subject: string; available: string; required: string; requiredLabel: string };
  /** Conclusion in source names; the complete assumptions are the context rows. */
  namedConclusion?: string;
  judgement?: { assumptions: string[]; conclusion: string; text: string };
  graph: GraphDefinition[];
  kind: string;
  kindLabel: string;
  /** The role's own name, where the record gives a specific one. */
  title: string;
  /** What that role means, in prose. */
  what: string;
  role: string;
  id: string;
  fuel: number;
  phase: string;
  pos: Span | null;
  /** Where the statement entry this obligation is about begins. */
  environmentStart?: number;
  /** The result type the request asked for, printed. */
  requiredResult?: string;
  rows: ContextRow[];
  /** The judgement required, for a node obligation. */
  conclusion?: string;
  term?: string;
  endpoints: Endpoint[];
  knowledge: KnowledgeRow[];
  knowledgeIsTheDifference?: boolean;
  observation?: string;
  note?: string;
}





// Roles come from extraction. An unknown role stays generic rather than being
// guessed into a more specific story.
const ROLE: Record<string, { title: string; what: string }> = {
  "return-contract": {
    title: "Return contract",
    what: "The value this returns must establish the function's declared result. The expression's own claim can be sound and still not do that.",
  },
  "expression-claim": {
    title: "Expression claim",
    what: "The type claimed for this expression had to follow from the assumptions in force here.",
  },
  "binding-annotation": {
    title: "Binding annotation",
    what: "The value bound here had to meet the annotation written on the binding.",
  },
  "closure-entry": {
    title: "Closure entry",
    what: "The closure's entry context had to follow from what is in scope where it is written.",
  },
  "closure-result": {
    title: "Closure result",
    what: "The closure body had to establish the result its contract declares. The span may be the whole lambda rather than its body.",
  },
  "heap-observation": {
    title: "Current-content assertion",
    what: "The cell facts asserted at this statement had to follow from the incoming edge. Every statement entry is a full local interface: only what is claimed there crosses it.",
  },
  "tag-dispatch": {
    title: "Tag dispatch",
    what: "This obligation comes from a tag test. What follows had to hold under the branch that test selects, read together with the observation rather than as plain subtyping.",
  },
  completion: {
    title: "Completing without returning",
    what: "This body can reach its end without returning. Completing produces undefined, and that value still has to establish the function's declared result. Nothing is claimed here for a reader to correct: the annotation is what does not hold.",
  },
  "node-typing": {
    title: "Obligation at this point",
    what: "The judgement attempted at this point did not follow from the assumptions available.",
  },
};
const roleView = (role: string) =>
  ROLE[role] || {
    title: "Obligation at this point",
    what: "This obligation's source role is not one this reader knows; it is shown as recorded.",
  };

const KIND_LABEL: Record<string, string> = {
  "node-typing": "node typing",
  "edge-coverage": "edge coverage",
  "expression-claim": "expression claim",
  "production-failure": "production failure",
};

/* ---------- types ---------- */
// A type is a list of labels into the record's own table, read as their union
// and printed in the one surface syntax every claim is shown in: lifted into
// the structural encoding and printed from there.
function typeText(types: any, labels: any, depth = 3) {
  if (!Array.isArray(labels)) return "(no type recorded)";
  return surface.printType(surface.lift(types, labels, null, depth)).text;
}

/* ---------- source maps ---------- */
// A descriptor says how one context binding is named in the source: a binding
// name, or the expression whose value it holds. Extraction guarantees one of the
// two for every binding and fails rather than emit a context it cannot describe,
// so a position should never reach a reader. The `slot N` fallback below is for
// a record that arrives without a source map at all; seeing one means the
// producer broke that invariant.
function bindingText(descriptor: any, source: string) {
  if (!descriptor) return "";
  if (descriptor.name) return descriptor.name;
  if (!Array.isArray(descriptor.span)) return "";
  return String(source || "")
    .slice(descriptor.span[0], descriptor.span[1])
    .replace(/\s+/g, " ")
    .trim();
}

const bindingsOf = (map: any, source: string) =>
  (map?.context || []).map((d: any) => bindingText(d, source));

/* ---------- current-content requirements ---------- */
// A slot's type is its standing contract; knowledge is a statement about the
// heap as it is at this point. Two ends can agree on every contract and still
// differ here, so these facts are shown in their own right rather than folded
// into the slot table. See ../OBLIGATION-DIAGNOSTICS.md.
const LITERAL: Record<string, string> = { nul: "null", tru: "true", fls: "false" };
const contentsText = (contents: any): any =>
  !Array.isArray(contents) || !contents.length
    ? "never"
    : contents.map((l) => LITERAL[l] || String(l)).join(" | ");

function knowledgeRows(knowledge: any, names: string[] = []) {
  if (!knowledge) return [];
  const of = (slot: any) => names[slot] || "slot " + slot;
  const rows: any[] = [];
  for (const f of knowledge.cells || [])
    rows.push({ slot: f.slot, binding: of(f.slot), what: "holds " + contentsText(f.contents) });
  for (const f of knowledge.values || [])
    rows.push({ slot: f.slot, binding: of(f.slot), what: "is " + contentsText(f.contents) });
  // A link relates two bindings, so it is listed against the one it constrains.
  for (const g of knowledge.links || [])
    rows.push({
      slot: g.value,
      binding: of(g.value),
      what: g.alias
        ? "is the same value as " + of(g.cell)
        : "is a read of " + of(g.cell),
    });
  return rows;
}

// Terms are shown technically: this is the calculus's own encoding, and naming
// it after a source construct would be a guess.
function termText(term: any): any {
  if (typeof term === "string") return term;
  if (term && term.var) return "slot " + term.var.i;
  return JSON.stringify(term);
}

/* ---------- one record, as rows a panel can show ---------- */
const sameType = (a: any, b: any) => JSON.stringify(a) === JSON.stringify(b);

// The destination map acts after the result is pushed: target slot i takes
// source slot mapping[i]. A null mapping selects the available context as it is.
function mapContext(available: any, mapping: any) {
  if (!Array.isArray(mapping)) return available;
  return mapping.map((slot) => available[slot]);
}

function obligationView(ob: any, source = "") {
  if (!ob) return null;
  const types = ob.types || [];
  // An edge fails at what its destination required, so a destination role that
  // names something specific describes it. A generic destination leaves the
  // source end to describe it, which is where a dispatch role sits.
  const specific = (o: any) => o && o.role && o.role !== "node-typing";
  const sourceMap =
    ob.kind === "edge-coverage" && specific(ob.destination?.sourceMap)
      ? ob.destination.sourceMap
      : ob.source?.sourceMap || ob.sourceMap || null;
  const role = roleView(sourceMap?.role);
  const view: ObligationView = {
    kind: ob.kind,
    kindLabel: KIND_LABEL[ob.kind] || ob.kind,
    role: sourceMap?.role || "",
    title: role.title,
    what: role.what,
    id: ob.id || "",
    fuel: ob.fuel,
    phase: ob.phase,
    pos: sourceMap?.pos || null,
    environmentStart: sourceMap?.environmentStart ?? null,
    requiredResult: ob.requiredResult
      ? typeText(types, ob.requiredResult)
      : "",
    rows: [],
    graph: [],
    endpoints: [],
    observation: undefined,
    note: "",
    // What the failing end required of the heap as it is, and whether that is
    // all that separates the two ends.
    knowledge: [],
    knowledgeIsTheDifference: false,
  };

  if (ob.kind === "edge-coverage") {
    const available = ob.transfer?.available || [];
    const required = ob.destination?.claim?.context || [];
    const mapped = mapContext(available, ob.transfer?.target?.mapping);
    const names = bindingsOf(ob.destination?.sourceMap, source);
    view.rows = required.map((need: any, slot: any) => ({
      slot,
      binding: names[slot] || "slot " + slot,
      have: typeText(types, mapped[slot]),
      need: typeText(types, need),
      differs: !sameType(mapped[slot], need),
    }));
    view.conclusion = "";
    view.endpoints = [
      { end: "from", sourceMap: ob.source?.sourceMap || null, label: ob.source?.label },
      {
        end: "to",
        sourceMap: ob.destination?.sourceMap || null,
        label: ob.transfer?.target?.label ?? ob.destination?.label,
      },
    ];
    // An observation is the premise the selected edge carries, never a statement
    // that execution took it. Boolean and tag dispatch both observe slot 0.
    const observed = ob.transfer?.booleanObservation;
    const tag = ob.transfer?.tagObservation;
    if (observed === true || observed === false)
      view.observation =
        "This edge carries the case where " +
        (names[0] || "slot 0") +
        " is " +
        observed +
        ". That is the edge's premise, not a claim that execution took it.";
    else if (tag && tag.test !== undefined)
      view.observation =
        "This edge carries the case where the tag test " +
        String(tag.test) +
        " answers " +
        String(tag.answer) +
        " on " +
        (names[tag.slot ?? 0] || "slot " + (tag.slot ?? 0)) +
        ". That is the edge's premise, not a claim that execution took it.";
    view.knowledge = knowledgeRows(ob.destination?.requiredKnowledge, names);
    const differing = view.rows.find((r) => r.differs);
    // Nothing here says which end is at fault; it says where the two ends stop
    // agreeing, which is all the record supports.
    view.knowledgeIsTheDifference = !differing && view.knowledge.length > 0;
    view.note =
      (differing
        ? differing.binding +
          " is where the available context and the destination's claim differ."
        : view.knowledgeIsTheDifference
          ? "Every binding's contract already agrees. What this edge had to establish beyond them is the current-content requirement above."
          : "The available context and the destination's claim agree on every binding.") +
      (ob.edgeIndex === undefined
        ? ""
        : " Both branch edges can share a destination; this is edge " +
          ob.edgeIndex +
          ".");
    return view;
  }

  const sequent = ob.sequent || {};
  const names = bindingsOf(sourceMap, source);
  view.rows = (sequent.context || []).map((entry: any, slot: any) => ({
    slot,
    binding: names[slot] || "slot " + slot,
    have: typeText(types, entry),
    // The source map names the saved result by the expression it came from; the
    // role is what says that this one is the value being returned.
    note:
      slot === 0 && sourceMap?.role === "return-contract"
        ? "the value being returned"
        : "",
  }));
  view.term = termText(sequent.term);
  view.conclusion = typeText(types, sequent.type);
  // A node obligation records its own required facts, when it has any.
  view.knowledge = knowledgeRows(ob.source?.requiredKnowledge, names);
  return view;
}

  const obligationReader = {
    typeText,
    termText,
    contentsText,
    knowledgeRows,
    bindingText,
    bindingsOf,
    mapContext,
    obligationView,
    roleView,
  };

export default obligationReader;
/** Uniform report contract: the UI renders these strings without decoding the
 * calculus or applying slot transfers. Keep the raw diagnostic beside it.
 * Edge goals name the transfer explicitly: heap facts cannot simply be copied
 * across calls/writes. JSON terms are the complete native term language.
 */
export function presentObligation(ob: ObligationDiagnostic, source: string): ObligationView {
  const view = obligationReader.obligationView(ob,source)!;
  view.graph = graphDefinitions(decodeGraph(ob.types));
  if (ob.kind === "production-failure") {
    view.title = "Certificate production stopped";
    view.what = ob.failure;
    return view;
  }
  const context = (entries: number[][], prefix = "slot") => entries.map((t,i) => `${prefix} ${i}: ${printLabels(t)}`);
  let assumptions: string[], conclusion: string;
  if (ob.kind === "edge-coverage") {
    const t = ob.transfer!;
    const differing = view.rows.find(r => r.differs);
    if (differing?.need) {
      view.focus = {subject:differing.binding,available:differing.have,required:differing.need,requiredLabel:"Required at destination"};
      view.summary = `The incoming claim for ${differing.binding} is ${differing.have}. The next point requires ${differing.need}.`;
    } else if (view.knowledge.length) {
      view.summary = "The incoming claims do not establish the required current-content facts below.";
    }
    assumptions = context(t.available,"available");
    if (t.booleanObservation !== null) assumptions.push(`available 0 = ${t.booleanObservation}`);
    if (t.tagObservation) assumptions.push(`${JSON.stringify(t.tagObservation.test)}(available ${t.tagObservation.slot}) = ${t.tagObservation.answer}`);
    assumptions.push(`source node = ${JSON.stringify(ob.source.node)}`);
    if (ob.source.requiredKnowledge) assumptions.push(`source heap requirements = ${JSON.stringify(ob.source.requiredKnowledge)}`);
    const mapping = t.target.mapping;
    const destination = ob.destination.claim!.context.map((type,i) =>
      `available ${mapping === null ? i : mapping[i]}: ${printLabels(type)}`);
    conclusion = `transfer to node ${t.target.label} establishes { ${destination.join(", ")} }`;
    if (ob.destination.requiredKnowledge) conclusion += ` and heap ${JSON.stringify(ob.destination.requiredKnowledge)}`;
  } else {
    const q = ob.sequent!;
    const slot = typeof q.term === "object" && "var" in q.term ? q.term.var.i : undefined;
    const row = slot === undefined ? undefined : view.rows.find(r => r.slot === slot);
    if (row) {
      const required = typeText(ob.types,q.type);
      const isReturn = view.role === "return-contract" || view.role === "closure-result";
      view.focus = {subject:row.binding,available:row.have,required,
        requiredLabel:isReturn ? "Required return type" : "Required type"};
      view.summary = `The available claim for ${row.binding} is ${row.have}. ${isReturn ? "This return" : "This obligation"} requires ${required}.`;
      view.namedConclusion = `${row.binding}: ${required}`;
    }
    assumptions = context(q.context);
    conclusion = `${printTerm(q.term)} : ${printLabels(q.type)}`;
  }
  view.judgement = {assumptions,conclusion,text:`${assumptions.length ? assumptions.join("; ") : "∅"} ⊢ ${conclusion}`};
  return view;
}
