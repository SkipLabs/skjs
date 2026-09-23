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
export const cases: Case[] = [
  positive(
    "generic-rigid-default",
    "A universally certified rigid default replaces omitted arguments without specializing T",
  ),
  positive(
    "default-deferred-capture",
    "Deferred closures capture initialized parameters while effectful defaults keep source order",
  ),
  negative(
    "invalid-default-invocation",
    "A default-created closure cannot be invoked while its capture is uninitialized",
    /pending closure cannot be invoked or exposed/,
  ),
  negative(
    "invalid-rigid-default",
    "A default must establish T universally even when every observed call uses boolean",
    /generic binding annotation.*cannot establish true ≤ T/,
  ),
  positive(
    "generic-defaults",
    "Universally certified default initialization before rigid results and callbacks",
  ),
  negative(
    "invalid-generic-default",
    "An observed Boolean call cannot justify a default for every T",
    /generic binding annotation.*cannot establish T ≤ boolean/,
  ),
  positive(
    "default-parameter-scope",
    "Sequential defaults, effects, and captured initialized parameters",
  ),
  gap(
    "default-later-parameter",
    "A later parameter is uninitialized while an earlier default runs",
    "unsupported",
    "proposal",
    /parameter default may only read initialized earlier parameters/,
  ),
  gap(
    "generic-default",
    "A generic default field write cannot be discarded when no certificate models it",
    "unverified",
    "search",
    /body requires a variable, a primitive literal, an assignment, a call or a closure/,
  ),
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
  positive(
    "optional-parameters",
    "omitted trailing arguments / optional parameter contracts",
  ),
  positive(
    "rest-parameters",
    "A tuple rest collected into a fresh array, read by index and in a closure",
  ),
  negative(
    "invalid-rest-element",
    "rest element returned at another position's contract",
  ),
  positive(
    "spread-arguments",
    "A tuple spread written in place of the last arguments, read after the others",
  ),
  negative(
    "invalid-spread-element",
    "spread element at another position's contract",
  ),
  positive(
    "rest-unbounded",
    "Array rests: any number of arguments, spreads among them read where written, a fixed-signature use, omission before the rest, and a callable field",
  ),
  negative("invalid-rest-actual", "an actual outside a rest's element type"),
  negative(
    "spread-holes",
    "TypeScript accepts a sparse Boolean array spread that puts undefined into a Boolean rest",
    /a spread of an array that may have holes passes `undefined`/,
  ),
  positive(
    "overloads",
    "one closure advertising two signatures, checked and called at each",
  ),
  positive(
    "default-parameters",
    "defaults replacing an omitted argument, including one reading an earlier parameter",
  ),
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
  // The optional parameter is read at its declared contract, which admits
  // `undefined`; returning it as a Boolean is an obligation, not an arity
  // question.
  negative(
    "invalid-optional-body",
    "optional parameter returned without its guard",
  ),
  // The default is checked against the type the body reads, like any other
  // expression obligation.
  // Each advertised signature is a separate obligation on the same body: the
  // Boolean one promises `true` and the body returns its argument.
  negative("invalid-overload", "signature the body does not implement"),
  negative(
    "invalid-default-parameter",
    "default value outside its parameter's contract",
  ),
  positive("generic-closure", "polymorphic closure / fresh call inference"),
  positive(
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
  positive(
    "generic-inference",
    "joined lower bounds / contravariant upper bounds",
  ),
  positive(
    "generic-dependent-inference",
    "propagated dependent inference bounds",
  ),
  positive(
    "generic-bounded",
    "bounded scheme / substituted bound at each call",
  ),
  positive(
    "generic-returned",
    "returned closure retaining the outer binder in its result",
  ),
  positive(
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
  positive(
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
  // A genuine bound violation survives inference: number cannot instantiate
  // a binder constrained to boolean, regardless of candidate selection.
  negative(
    "invalid-bound-argument",
    "substituted bound obligation",
    /does not satisfy the closure's bound: cannot establish number ≤ boolean/,
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
