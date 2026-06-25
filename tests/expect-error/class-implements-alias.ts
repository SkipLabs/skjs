// `class C implements TypeAlias` when TypeAlias is an object-typed type alias.
// tsc accepts this; the class must structurally satisfy the alias. skjs
// currently fails with "A class name was expected here" for any type alias in
// an implements clause, because the implements loop resolves the name only
// against class/interface definitions.
//
// The error annotations below document the current bug. The positive cases
// (valid implementations of object-typed aliases) will have their annotations
// removed when the fix lands; the negative cases (non-object aliases, TS2422;
// incompatible members, TS2420) will keep annotations but with updated messages.

type Shape = { readonly area: number };

// tsc: OK — object-type alias is a valid implements target.
// skjs (bug): "A class name was expected here"
// @skjs-expect-error A class name was expected here
class Circle implements Shape {
  readonly area: number = 3;
}

// tsc: OK — class satisfies multiple object-type alias implements clauses.
// skjs (bug): "A class name was expected here"
type HasName = { readonly name: string };
// @skjs-expect-error A class name was expected here
class Named implements Shape, HasName {
  readonly area: number = 0;
  readonly name: string = "";
}

// tsc: TS2420 — class incorrectly implements alias (wrong member type).
// skjs (bug): "A class name was expected here" instead of TS2420.
type HasX = { readonly x: number };
// @skjs-expect-error A class name was expected here
class BadImpl implements HasX {
  readonly x: string = "bad";
}

// tsc: TS2422 — union alias is not a valid implements target.
// skjs (bug): "A class name was expected here" instead of TS2422.
type UnionAlias = { a: number } | { b: string };
// @skjs-expect-error A class name was expected here
class ForUnion implements UnionAlias {
  a: number = 1;
}

// tsc: TS2422 — primitive alias is not a valid implements target.
// skjs (bug): "A class name was expected here" instead of TS2422.
type PrimAlias = string;
// @skjs-expect-error A class name was expected here
class ForPrim implements PrimAlias {}

// tsc: OK — generic object-type alias with type argument propagation.
// skjs (bug): "A class name was expected here"
type Wrapper<T> = { readonly wrapped: T };
// @skjs-expect-error A class name was expected here
class Wrap<T> implements Wrapper<T> {
  readonly wrapped: T;
  constructor(v: T) {
    this.wrapped = v;
  }
}
