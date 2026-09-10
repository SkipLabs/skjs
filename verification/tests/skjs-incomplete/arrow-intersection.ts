/**
 * Producer precision gap: an intersection of two arrows with disjoint domains
 * is inhabited, by any function that meets both signatures, and TypeScript
 * accepts this one. SKJS computes the intersection of two function types as
 * whichever is a subtype of the other, and as `never` when neither is, so it
 * rejects the binding with "is not assignable to type 'never'" and, under
 * keep-going collection, exports `f` at the empty type. The verifier proves
 * the lambda once under each signature and resolves the call to the first
 * signature admitting its argument; with the intersection claimed as the
 * source declares it, the function verifies (tests/source-claims.js).
 */
function meetsBoth(): null {
  const f: ((x: true) => null) & ((x: false) => null) = (x: boolean): null =>
    null;
  return f(true);
}
