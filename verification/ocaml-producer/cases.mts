// Executable coverage inventory. A negative control must reach validation;
// an earlier gate failure cannot masquerade as a soundness regression passing.
import type { Outcome, Phase } from "./check.mts";
export interface Case {
  file: string;
  area: string;
  kind: "positive" | "negative" | "gap";
  status: Outcome["status"];
  phase: Phase;
  diagnostic?: RegExp;
}
const positive = (file: string, area: string): Case => ({
  file,
  area,
  kind: "positive",
  status: "verified",
  phase: "check",
});
const negative = (
  file: string,
  area: string,
  diagnostic = /evidence search failed/,
): Case => ({
  file,
  area,
  kind: "negative",
  status: "unverified",
  phase: "search",
  diagnostic,
});
const gap = (
  file: string,
  area: string,
  status: Outcome["status"],
  phase: Phase,
  diagnostic: RegExp,
): Case => ({ file, area, kind: "gap", status, phase, diagnostic });
const certificateGap = (file: string, area: string): Case =>
  gap(
    file,
    area,
    "unverified",
    "check",
    /(?:generic body|quantified callable) has no (?:universal )?semantic certificate/,
  );
export const cases: Case[] = [
  positive("values", "immutable snapshots / fixed storage"),
  positive("branches", "branch scopes / arithmetic"),
  positive("objects", "multi-field objects / aliases"),
  positive("callbacks", "higher-order calls / variance / capture"),
  positive("generics", "rigid parameters / bounds"),
  positive("contextual", "contextual object and tuple construction"),
  positive("readonly", "readonly capabilities / covariance"),
  positive("arrays", "array writes / tuple presence"),
  positive("flow", "immutable refinements / nullish paths"),
  positive("loops", "loop invariants / break / continue"),
  positive("blocks-bind", "closure scopes / partial application"),
  positive("aliases", "capture-avoiding alias substitution"),
  positive("top-void", "unknown / discarded callback result"),
  positive("function-fields", "one object with fields and calls"),
  negative("invalid-return", "return contract"),
  negative("invalid-local-write", "fixed storage contract"),
  negative("invalid-callback", "argument contract"),
  negative("invalid-variance", "contravariance"),
  negative("invalid-write", "aliased write"),
  negative("invalid-capture", "captured storage"),
  negative(
    "invalid-generic",
    "rigid fabrication",
    /generic.*(return|result)|not.*(bound|subtype)/,
  ),
  negative(
    "invalid-generic-copy",
    "inference cannot identify rigid parameters",
    /generic return contract at \[\d+,\d+\): cannot establish T ≤ U/,
  ),
  negative("invalid-readonly", "readonly write"),
  negative("invalid-array-write", "array write contract"),
  negative("invalid-tuple", "contextual tuple element obligation"),
  negative("invalid-context", "fresh initializer obligation"),
  negative("invalid-heap-refinement", "heap refinement invalidation"),
  certificateGap("generic-closure", "polymorphic closure / fresh call inference"),
  certificateGap(
    "generic-two-calls",
    "one scheme, two independently substituted eliminations",
  ),
  negative(
    "invalid-generic-closure",
    "universally quantified closure body",
    /cannot establish true ≤ T for every instantiation of \[T\]/,
  ),
  // Every observed call instantiates T at boolean, so the compiled arrow is
  // satisfied: only the universal gate separates this from specialization.
  negative(
    "invalid-scheme-capture",
    "scheme valid at every observed call but not universally",
    /cannot establish boolean ≤ T for every instantiation of \[T\]/,
  ),
  positive("generic-inferred", "inferred rigid copies / dependent bounds"),
  certificateGap("generic-bounded", "bounded scheme / substituted bound at each call"),
  certificateGap(
    "generic-returned",
    "returned closure retaining the outer binder in its result",
  ),
  certificateGap(
    "generic-captured-store",
    "quantified closure reading a captured cell at one fixed contract",
  ),
  // A write into the captured cell is an obligation on the value against the
  // cell's fixed contract; `T` never meets `number`, whatever the calls.
  negative(
    "invalid-captured-write",
    "captured cell written at the binder's type",
    /captured storage write at \[\d+,\d+\): cannot establish T ≤ number under \[T\]/,
  ),
  certificateGap(
    "generic-callback",
    "binder inferred through a callback parameter and a callback result",
  ),
  // The callback's parameter is checked contravariantly against the
  // substituted signature at the graph: a `number` callback cannot take `T`
  // at boolean, whatever the producer proposed.
  negative("invalid-callback-variance", "callback parameter variance"),
  negative(
    "invalid-callback-result",
    "closure fabricating a result the callback should supply",
    /does not satisfy its scheme universally: cannot establish boolean ≤ T/,
  ),
  // The nested body is checked under the outer binders like the outer body:
  // a capture that happens to fit every observed call is still not `T`.
  negative(
    "invalid-returned-capture",
    "nested closure body against its rigid result",
    /does not satisfy its scheme universally: cannot establish boolean ≤ T/,
  ),
  // The reversed bound is an elimination obligation at the call, under the
  // closure's declared parameters: the inclusion that failed, by name.
  negative(
    "invalid-bound-reversed",
    "substituted bound obligation",
    /does not satisfy the closure's bound: cannot establish boolean ≤ true under \[U, T ≤ U\]/,
  ),
  // The bound justifies T ≤ U, never U ≤ T; every observed call could still
  // agree, so only introduction refuses it.
  negative(
    "invalid-bound-body",
    "reversed bound in a scheme body",
    /does not satisfy its scheme universally: cannot establish U ≤ T/,
  ),
  gap(
    "unsupported",
    "inferred lifetime contract",
    "unsupported",
    "proposal",
    /explicit fixed storage contract/,
  ),
  gap(
    "dynamic-index",
    "arbitrary numeric indexing",
    "unverified",
    "search",
    /proved array-index singleton/,
  ),
  gap(
    "optional-field",
    "optional field presence",
    "unsupported",
    "source",
    /required mutable field/,
  ),
  gap("bare-return", "bare return", "unsupported", "source", /bare `return`/),
  gap(
    "empty-closure",
    "implicit closure completion",
    "unsupported",
    "source",
    /return on both terminal arms/,
  ),
];
