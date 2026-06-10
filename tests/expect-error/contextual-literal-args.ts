// A fresh literal element of an array literal stays precise until the literal
// commits against a target type, instead of being widened to its base type at
// the expression. An inline array literal whose key is the literal `0`
// therefore matches a parameter instantiated at `<0, ...>`, mirroring a
// singleton-row update whose key is fixed to `0`. A non-matching literal key
// is still rejected.

declare function update<K, V>(
  collection: string,
  entries: Array<[K, V[]]>,
): void;

// Inline nested literal: `0` stays `'0'` when checked against the explicit `<0>`.
function inlineLiteralKey(): void {
  update<0, { value: number }>("counter", [[0, [{ value: 1 }]]]);
}

// The same payload bound to a `const` first is also accepted.
// FIXME: TypeScript rejects this. A `const`-bound array literal is not deeply
// frozen, so `entries` widens to `(number | { value: number }[])[][]`, losing
// the tuple shape and the literal `0`; SKJS keeps it precise and accepts.
function variableLiteralKey(): void {
  const entries = [[0, [{ value: 1 }]]];
  update<0, { value: number }>("counter", entries);
}

// A non-matching literal key is rejected.
function mismatchedLiteralKey(): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  // @skjs-expect-error-line2 Type '1'
  // @skjs-expect-error-line3 is not assignable to type '0'
  // @skjs-expect-error-line4 Value '1' is missing
  update<0, { value: number }>("counter", [[1, [{ value: 1 }]]]);
}

// Each literal kind stays precise: string and boolean against array and tuple
// targets (cases 2b and 2c), bigint, negative, and unary-plus numbers.
function stringElements(): void {
  const tags: ("urgent" | "priority")[] = ["urgent", "priority"];
}
function booleanElements(): void {
  const flags: [true, false] = [true, false];
}
function bigintElements(): void {
  const bigs: Array<1n> = [1n];
}
function negativeElements(): void {
  const negs: [-1, number] = [-1, 5];
}
function unaryPlusElements(): void {
  const ones: Array<1> = [+1];
}

// A mismatched string literal is still rejected.
function mismatchedStringElement(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  // @skjs-expect-error-line2 Type 'other' | 'priority' | 'urgent'
  // @skjs-expect-error-line3 is not assignable to type 'priority' | 'urgent'
  // @skjs-expect-error-line4 Value 'other' is missing
  const tags: ("urgent" | "priority")[] = ["urgent", "other"];
}

// Inference under a literal-bearing constraint: the fresh element satisfies
// the constraint, so the call checks; K resolves to the constraint.
declare function pick<K extends 0 | 1>(entries: Array<[K, number]>): K;
function constraintSatisfied(): void {
  const k: 0 | 1 = pick([[0, 1]]);
}
function constraintViolated(): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  // @skjs-expect-error-line2 Type '5'
  // @skjs-expect-error-line3 is not assignable to type '0' | '1'
  let r: 0 | 1 = pick([[5, 1]]);
}

// FIXME: TypeScript unions the inference candidates (K = 0 | 1) and accepts;
// SKJS pins K to '0' from the array element and rejects the second argument,
// whose fresh literal `1` is widened to number in this (non-const) context.
declare function pickBoth<K extends 0 | 1>(
  entries: Array<[K, string]>,
  key: K,
): K;
function firstCommitmentPinning(): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  // @skjs-expect-error-line2 Full type number
  // @skjs-expect-error-line3 is not assignable to specific type '0'
  let r: 0 | 1 = pickBoth([[0, "a"]], 1);
}
