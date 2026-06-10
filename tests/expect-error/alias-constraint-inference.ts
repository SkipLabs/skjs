// A generic type-alias parameter's constraint is enforced in an ambient
// declaration. In `f`'s signature, `Id<P extends string>` is instantiated with
// the unconstrained type parameter V (`x: Id<V>`); V does not satisfy
// `P extends string`, so the declaration is rejected — the same place TypeScript
// rejects it (TS2344). The call site cannot then reach the boundary.

type Id<P extends string> = P;

declare function f<V>(x: Id<V>): V;

export function usesRejectedBoundary(): number {
  return f(42);
}
