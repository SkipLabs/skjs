// `as const` on an array literal produces a readonly tuple whose element
// types are the elements' own `as const` types (issue #949).
//
// The cases live inside functions because a top-level `const` must have a
// primitive type in SKJS, and a readonly tuple is an object type.
//
// Every case below is in a most-precise (const) context, where SKJS reports an
// `as const` as unnecessary. That is a known false positive when the assertion
// is load-bearing (it makes a mutable literal readonly); it is a warning, not
// an error, so it does not block these programs (see #951).

// Regression for #949: a tuple literal with `as const` in argument position,
// against a readonly-tuple generic constraint. tsc accepts this (K = readonly
// [0, 1]).
declare function pd<K extends readonly [0, 1]>(k: K): K;
function repro(): void {
  // @skjs-expect-warning This 'as const' is unnecessary
  const r = pd([0, 1] as const);
}

// A readonly-tuple annotation accepts the const-asserted literal: the element
// types stay the precise literals `0` and `1`.
function annotated(): void {
  // @skjs-expect-warning This 'as const' is unnecessary
  const t: readonly [0, 1] = [0, 1] as const;
}

// ...and a mismatched readonly-tuple annotation is rejected, so the literal
// element types really are checked (0 is not 1).
function mismatch(): void {
  // @skjs-expect-warning This 'as const' is unnecessary
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const t: readonly [1, 2] = [0, 1] as const;
}

// Nested array literals become nested readonly tuples.
function nested(): void {
  // @skjs-expect-warning This 'as const' is unnecessary
  const t = [
    [0, 1],
    [2, 3],
  ] as const;
}

// A non-literal element keeps its (precise) type in a readonly position.
function withVar(x: number): void {
  // @skjs-expect-warning This 'as const' is unnecessary
  const t = [x] as const;
}

// The empty array literal is the empty readonly tuple.
function emptyArr(): void {
  // @skjs-expect-warning This 'as const' is unnecessary
  const t = [] as const;
}

// The result is genuinely readonly: it is not assignable to a mutable tuple
// even when the element types match, so only the readonly modifier differs
// (tsc: TS4104).
function notAssignableToMutable(): void {
  // @skjs-expect-warning This 'as const' is unnecessary
  const t = [0, 1] as const;
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const m: [0, 1] = t;
}

// Regression guards for pathological operands (all still rejected, none crash):

// `!` applied to an array literal under `as const`: reported as a misused
// const assertion (like the object case), not as "'!' cannot be applied".
function bangArrayLiteral(): void {
  // @skjs-expect-warning This 'as const' is unnecessary
  // @skjs-expect-error A 'const' assertion can only be applied to a string, number, boolean, array, or object literal
  // @skjs-expect-error A condition is expected to be of type boolean or a type with a single falsy value
  const t = ![1, 2] as const;
}

// Unary '-' applied to an array literal with a non-literal element under
// `as const`: rejected without re-typing the element (must not crash).
function negArrayVar(x: number): void {
  // @skjs-expect-warning This 'as const' is unnecessary
  // @skjs-expect-error A 'const' assertion can only be applied to a string, number, boolean, array, or object literal
  // @skjs-expect-error Unary operator '-' cannot be applied to this type
  const t = -[x] as const;
}
