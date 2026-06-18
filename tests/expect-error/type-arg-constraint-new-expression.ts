// An explicit type argument on a `new` expression is checked against the class
// type parameter's constraint. This goes through the constructor-setup path,
// distinct from the reference-site check that normalize applies to a class named
// in a type position. A violating argument is rejected (TS2344, as TypeScript
// does); a satisfying one is accepted.

class Box<T extends string> {
  v?: T;
}

function violating(): void {
  // @skjs-expect-error Type argument does not satisfy the constraint
  const bad = new Box<number>();
}

function satisfying(): void {
  const good = new Box<"literal">();
}
