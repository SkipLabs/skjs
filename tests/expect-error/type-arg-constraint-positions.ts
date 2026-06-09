// Type-argument constraints are enforced wherever a generic type is referenced —
// in alias bodies, interface fields, and function signatures — not only when the
// type is later expanded. Each violating reference is rejected at its site, the
// same place TypeScript rejects it (TS2344), and arguments that satisfy the
// constraint are accepted.

type Id<P extends string> = P;

// @ts-expect-error Constraint not satisfied
type AliasBody = Id<number>;

interface Field {
  // @ts-expect-error Constraint not satisfied
  x: Id<number>;
}

// @ts-expect-error Constraint not satisfied
function defParam(x: Id<number>): void {}

// @ts-expect-error Constraint not satisfied
function defTparam<V>(x: Id<V>): V {
  return x;
}

// A used ambient declaration is checked when its signature is normalized at the
// use site.
// @ts-expect-error Constraint not satisfied
declare function usedDecl<V>(x: Id<V>): V;
export function usesDecl(): number {
  return usedDecl(42);
}

// Valid: arguments that satisfy the constraint are accepted.
type ValidAlias = Id<"literal">;
interface ValidField {
  x: Id<string>;
}
function validParam(x: Id<string>): void {}
function validTparam<V extends string>(x: Id<V>): V {
  return x;
}
