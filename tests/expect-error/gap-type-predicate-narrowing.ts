// A user-defined type predicate's narrowing effect is not modelled: skjs
// accepts the `x is T` syntax on a declared signature (since #733) but does
// not narrow the argument in the truthy branch, so a property access on the
// still-`unknown` value is rejected. Surfaced by the regenerated
// generated-examples (key-value-store, via isJsonObject).
// FIXME(#582): skjs should narrow via user-defined type predicates; tsc accepts.
declare function isString(x: unknown): x is string;
export function typePredicateNarrowing(x: unknown): number {
  if (isString(x)) {
    // @skjs-expect-error Cannot access a property on type unknown
    return x.length;
  }
  return 0;
}
