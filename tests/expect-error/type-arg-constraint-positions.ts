// Type-argument constraints are enforced wherever a generic type is referenced —
// in alias bodies, interface fields, and function signatures — not only when the
// type is later expanded. Each violating reference is rejected at its site, the
// same place TypeScript rejects it (TS2344), and arguments that satisfy the
// constraint are accepted.

type Id<P extends string> = P;

// @skjs-expect-error Type argument does not satisfy the constraint
type AliasBody = Id<number>;

interface Field {
  // @skjs-expect-error Type argument does not satisfy the constraint
  x: Id<number>;
}

// @skjs-expect-error Type argument does not satisfy the constraint
function defParam(x: Id<number>): void {}

// @skjs-expect-error Type argument does not satisfy the constraint
function defTparam<V>(x: Id<V>): V {
  return x;
}

// An ambient declaration is checked at its declaration site, the same as a
// function with a body.
// @skjs-expect-error Type argument does not satisfy the constraint
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
