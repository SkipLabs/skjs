// Unsoundness demo: a generic type-alias parameter's constraint is bypassed
// when the alias is instantiated with an inferred type variable.
//
// `Id<P extends string>` is head-transparent (`Id<X>` expands to `X`). Inferring
// V from the argument through the alias-typed parameter `x: Id<V>` checks the
// `P extends string` constraint against the still-unbound inference variable (so
// it passes vacuously) and never re-validates after V resolves to `number`.
// skjs accepts `f(42)` with V = number.
//
// TypeScript rejects this at the declaration:
//   error TS2344: Type 'V' does not satisfy the constraint 'string'.
// The explicit form `f<number>(42)` and a direct `<V extends string>` parameter
// are both rejected by skjs too, so the gap is specific to inference through the
// alias. See tests/repro/unsound-expansion-crash/ for the runtime TypeError this
// produces when the boundary is a typed library implemented in JS.
//
// NOTE: this file is deliberately not tsc-clean. tsc rejects the declaration
// above, which would normally call for a ts-expect-error directive there, but
// the skjs harness requires skjs to actually report an error at every annotated
// line and skjs reports none (that is the bug). It is kept here unannotated to
// document the gap; it must be made clean (skjs rejecting the call, annotation
// added) before landing to main.

type Id<P extends string> = P;

declare function f<V>(x: Id<V>): V;

export function unsoundlyAcceptsNumber(): number {
  return f(42);
}
