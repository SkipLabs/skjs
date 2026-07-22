// A value whose type refers to itself through `typeof` (issue #999).
//
// `typeof v` reads v's declared type, so a value typed as its own `typeof`,
// directly or through other values, has a type that requires itself. Until the
// cycle was cut, resolving one of these never terminated. tsc reports TS2502 on
// each value in the cycle; SKJS reports it once, at the reference that closes
// the cycle, which is inside one of the declarations rather than at the use
// that triggers the resolution.
//
// A value declaration's annotation is not resolved on its own, so each cycle
// carries a use below to trigger it.

// A value typed as its own typeof: the reference closes the cycle on the same
// line it opens it.
// @skjs-expect-error 'selfV' is referenced directly or indirectly in its own type annotation
declare const selfV: typeof selfV;
type UseSelf = typeof selfV;

// Two values, each typed as the other's typeof. The cycle closes on the second
// declaration, where `mutualV` is named again.
declare const mutualV: typeof mutualW;
// @skjs-expect-error 'mutualV' is referenced directly or indirectly in its own type annotation
declare const mutualW: typeof mutualV;
type UseMutual = typeof mutualV;

// A longer cycle through three values, closing on the third declaration.
declare const cycleA: typeof cycleB;
declare const cycleB: typeof cycleC;
// @skjs-expect-error 'cycleA' is referenced directly or indirectly in its own type annotation
declare const cycleC: typeof cycleA;
type UseCycle = typeof cycleA;

/////////////////////////////////////////////////////////////////////////////
// Legal: a value's typeof that does not lead back to itself.
/////////////////////////////////////////////////////////////////////////////

// Resolving through another value that is not part of a cycle is fine.
declare const base: { a: string };
declare const alias: typeof base;
type UseAlias = typeof alias;

// The same value named by two different aliases is not a cycle.
declare const shared: { b: number };
type First = typeof shared;
type Second = typeof shared;
