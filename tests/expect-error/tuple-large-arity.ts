// Tuples are synthesized in TEnv::tuple without going through any
// predefined `TupleN` / `ReadonlyTupleN` interfaces, so arities beyond
// the historical 10-element cap work end-to-end.

// Arity-11: positional access, length, destructuring.
function fromArity11(): [
  number,
  number,
  number,
  number,
  number,
  number,
  number,
  number,
  number,
  number,
  number,
] {
  // @skjs-expect-error Invalid return type
  return [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];
}

function arity11Length(
  t: [
    number,
    number,
    number,
    number,
    number,
    number,
    number,
    number,
    number,
    number,
    number,
  ],
): 11 {
  return t.length;
}

function arity11Destructure(
  t: [
    number,
    string,
    boolean,
    number,
    string,
    boolean,
    number,
    string,
    boolean,
    number,
    string,
  ],
): string {
  const [, , , , , , , , , , last] = t;
  return last;
}

// Arity-15 with mixed types and readonly variant.
function readonlyArity15(
  // @skjs-expect-error TODO readonly
  t: readonly [
    number,
    string,
    boolean,
    number,
    string,
    boolean,
    number,
    string,
    boolean,
    number,
    string,
    boolean,
    number,
    string,
    boolean,
  ],
  // @skjs-expect-error TODO readonly
): readonly [
  number,
  string,
  boolean,
  number,
  string,
  boolean,
  number,
  string,
  boolean,
  number,
  string,
  boolean,
  number,
  string,
  boolean,
] {
  return t;
}

// Wrong-position type at arity > 10: still caught.
function arity12WrongPosition(
  t: [
    number,
    number,
    number,
    number,
    number,
    number,
    number,
    number,
    number,
    number,
    number,
    string,
  ],
): number {
  // @skjs-expect-error Invalid return type
  return t[11];
}
