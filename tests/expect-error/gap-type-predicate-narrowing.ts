// A declared user-defined type predicate (`x is T`) narrows the argument in
// the truthy branch (SkipLabs/skjs#582). Previously, skjs accepted the syntax
// on declared signatures (#733) but did not narrow, rejecting `x.length`.
declare function isString(x: unknown): x is string;
export function typePredicateNarrowing(x: unknown): number {
  if (isString(x)) {
    return x.length;
  }
  return 0;
}
