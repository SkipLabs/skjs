"use strict";
/* Reading an obligation diagnostic for display.
 *
 * A record describes an unsuccessful verification attempt: the assumptions that
 * were available and the conclusion that had to follow. It is explanatory
 * metadata, never proof evidence and never a judgement that a claim is false.
 * See ../OBLIGATION-DIAGNOSTICS.md. Everything here is pure, so the tests can
 * exercise it without a browser.
 */

const obligationReader = (() => {
const OBLIGATION_VERSION = 1;

// Roles come from extraction. An unknown role stays generic rather than being
// guessed into a more specific story.
const ROLE = {
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
  "node-typing": {
    title: "Obligation at this point",
    what: "The judgement attempted at this point did not follow from the assumptions available.",
  },
};
const roleView = (role) =>
  ROLE[role] || {
    title: "Obligation at this point",
    what: "This obligation's source role is not one this reader knows; it is shown as recorded.",
  };

const KIND_LABEL = {
  "node-typing": "node typing",
  "edge-coverage": "edge coverage",
  "expression-claim": "expression claim",
  "production-failure": "production failure",
};

/* ---------- types ---------- */
// A type is a list of labels into the record's own table, read as their union.
// Unknown clauses are shown as their encoding rather than guessed at, and
// recursion through references and arrows is cut off with an ellipsis: the
// graph is finite but may be cyclic.
function clauseText(types, clause, depth) {
  if (clause === "nul") return "null";
  if (clause === "bool") return "boolean";
  if (clause && clause.boolLit) return String(clause.boolLit.value);
  if (depth <= 0) return "…";
  if (clause && clause.refs) {
    const first = typeText(types, clause.refs.first, depth - 1);
    const rest = (clause.refs.rest || []).length
      ? " & " + clause.refs.rest.map((r) => typeText(types, r, depth - 1)).join(" & ")
      : "";
    return "Ref<" + first + ">" + rest;
  }
  if (clause && clause.arrs)
    return (clause.arrs.arrows || [])
      .map(
        ([domain, result]) =>
          "(" +
          typeText(types, domain, depth - 1) +
          ") => " +
          typeText(types, result, depth - 1),
      )
      .join(" & ");
  return JSON.stringify(clause);
}

function typeText(types, labels, depth = 3) {
  if (!Array.isArray(labels)) return "(no type recorded)";
  if (!labels.length) return "never";
  return labels
    .map((label) => {
      const node = types?.[label];
      if (!Array.isArray(node)) return "type " + label;
      return node.map((clause) => clauseText(types, clause, depth)).join(" | ");
    })
    .join(" | ");
}

/* ---------- current-content requirements ---------- */
// A slot's type is its standing contract; knowledge is a statement about the
// heap as it is at this point. Two ends can agree on every contract and still
// differ here, so these facts are shown in their own right rather than folded
// into the slot table. See ../OBLIGATION-DIAGNOSTICS.md.
const LITERAL = { nul: "null", tru: "true", fls: "false" };
const contentsText = (contents) =>
  !Array.isArray(contents) || !contents.length
    ? "never"
    : contents.map((l) => LITERAL[l] || String(l)).join(" | ");

function knowledgeRows(knowledge) {
  if (!knowledge) return [];
  const rows = [];
  for (const f of knowledge.cells || [])
    rows.push({ slot: f.slot, what: "cell holds " + contentsText(f.contents) });
  for (const f of knowledge.values || [])
    rows.push({ slot: f.slot, what: "value is " + contentsText(f.contents) });
  // A link relates two slots, so it is listed against the slot it constrains.
  for (const g of knowledge.links || [])
    rows.push({
      slot: g.value,
      what: g.alias
        ? "same value as slot " + g.cell
        : "read of the cell in slot " + g.cell,
    });
  return rows;
}

// Terms are shown technically: this is the calculus's own encoding, and naming
// it after a source construct would be a guess.
function termText(term) {
  if (typeof term === "string") return term;
  if (term && term.var) return "slot " + term.var.i;
  return JSON.stringify(term);
}

/* ---------- one record, as rows a panel can show ---------- */
const sameType = (a, b) => JSON.stringify(a) === JSON.stringify(b);

// The destination map acts after the result is pushed: target slot i takes
// source slot mapping[i]. A null mapping selects the available context as it is.
function mapContext(available, mapping) {
  if (!Array.isArray(mapping)) return available;
  return mapping.map((slot) => available[slot]);
}

function obligationView(ob) {
  if (!ob || ob.version !== OBLIGATION_VERSION) return null;
  const types = ob.types || [];
  // An edge fails at what its destination required, so a destination role that
  // names something specific describes it. A generic destination leaves the
  // source end to describe it, which is where a dispatch role sits.
  const specific = (o) => o && o.role && o.role !== "node-typing";
  const origin =
    ob.kind === "edge-coverage" && specific(ob.destination?.origin)
      ? ob.destination.origin
      : ob.source?.origin || ob.origin || null;
  const role = roleView(origin?.role);
  const view = {
    kind: ob.kind,
    kindLabel: KIND_LABEL[ob.kind] || ob.kind,
    role: origin?.role || "",
    title: role.title,
    what: role.what,
    id: ob.id || "",
    fuel: ob.fuel,
    phase: ob.phase,
    pos: origin?.pos || null,
    environmentStart: origin?.environmentStart ?? null,
    requiredResult: ob.requiredResult
      ? typeText(types, ob.requiredResult)
      : "",
    rows: [],
    endpoints: [],
    observation: null,
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
    view.rows = required.map((need, slot) => ({
      slot,
      have: typeText(types, mapped[slot]),
      need: typeText(types, need),
      differs: !sameType(mapped[slot], need),
    }));
    view.conclusion = "";
    view.endpoints = [
      { end: "from", origin: ob.source?.origin || null, label: ob.source?.label },
      {
        end: "to",
        origin: ob.destination?.origin || null,
        label: ob.transfer?.target?.label ?? ob.destination?.label,
      },
    ];
    // An observation is the premise the selected edge carries, never a statement
    // that execution took it. Boolean and tag dispatch both observe slot 0.
    const observed = ob.transfer?.booleanObservation;
    const tag = ob.transfer?.tagObservation;
    if (observed === true || observed === false)
      view.observation =
        "This edge carries the case where slot 0 is " +
        observed +
        ". That is the edge's premise, not a claim that execution took it.";
    else if (tag && tag.test !== undefined)
      view.observation =
        "This edge carries the case where the tag test " +
        String(tag.test) +
        " answers " +
        String(tag.answer) +
        " on slot " +
        (tag.slot ?? 0) +
        ". That is the edge's premise, not a claim that execution took it.";
    view.knowledge = knowledgeRows(ob.destination?.requiredKnowledge);
    const differing = view.rows.find((r) => r.differs);
    // Nothing here says which end is at fault; it says where the two ends stop
    // agreeing, which is all the record supports.
    view.knowledgeIsTheDifference = !differing && view.knowledge.length > 0;
    view.note =
      (differing
        ? "Slot " +
          differing.slot +
          " is where the available context and the destination's claim differ."
        : view.knowledgeIsTheDifference
          ? "Every slot's contract already agrees. What this edge had to establish beyond them is the current-content requirement above."
          : "The available context and the destination's claim agree on every slot.") +
      (ob.edgeIndex === undefined
        ? ""
        : " Both branch edges can share a destination; this is edge " +
          ob.edgeIndex +
          ".");
    return view;
  }

  const sequent = ob.sequent || {};
  view.rows = (sequent.context || []).map((entry, slot) => ({
    slot,
    have: typeText(types, entry),
    // The record says slot 0 holds the saved result at a return contract; every
    // other slot is a de Bruijn position, not a named source binding.
    note:
      slot === 0 && origin?.role === "return-contract"
        ? "the value being returned"
        : "",
  }));
  view.term = termText(sequent.term);
  view.conclusion = typeText(types, sequent.type);
  // A node obligation records its own required facts, when it has any.
  view.knowledge = knowledgeRows(ob.source?.requiredKnowledge);
  return view;
}

  return {
    OBLIGATION_VERSION,
    typeText,
    clauseText,
    termText,
    contentsText,
    knowledgeRows,
    mapContext,
    obligationView,
    roleView,
  };
})();

if (typeof module !== "undefined") module.exports = obligationReader;
