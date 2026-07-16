// `class C implements TypeAlias` when TypeAlias is an object-typed type alias.
// tsc accepts this; the class must structurally satisfy the alias. skjs
// resolves the implements clause through the alias (no class hierarchy
// recording — implements contributes no members, only the conformance check).

type Shape = { readonly area: number };

// Object-type alias: accepted.
class Circle implements Shape {
  readonly area: number = 3;
}

// Multiple object-type alias implements clauses: accepted.
type HasName = { readonly name: string };
class Named implements Shape, HasName {
  readonly area: number = 0;
  readonly name: string = "";
}

// Incompatible member type: TS2420 (class incorrectly implements).
type HasX = { readonly x: number };
// @skjs-expect-error This class incorrectly implements 'HasX'
class BadImpl implements HasX {
  readonly x: string = "bad";
}

// Union alias: TS2422 (must reference an interface or class, not a union).
type UnionAlias = { a: number } | { b: string };
// @skjs-expect-error An 'implements' clause must reference an interface or class
class ForUnion implements UnionAlias {
  a: number = 1;
}

// Primitive alias: TS2422.
type PrimAlias = string;
// @skjs-expect-error An 'implements' clause must reference an interface or class
class ForPrim implements PrimAlias {}

// Generic object-type alias with type argument propagation: accepted.
type Wrapper<T> = { readonly wrapped: T };
class Wrap<T> implements Wrapper<T> {
  readonly wrapped: T;
  constructor(v: T) {
    this.wrapped = v;
  }
}
