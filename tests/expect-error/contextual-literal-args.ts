// Contextual typing keeps a fresh literal precise when it is checked against a
// literal-typed parameter, instead of widening it to its base type. An inline
// array literal whose key is the literal `0` therefore matches a parameter
// instantiated at `<0, ...>`, mirroring a singleton-row update whose key is
// fixed to `0`. A non-matching literal key is still rejected.

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
  // @skjs-expect-error Invalid call
  // @skjs-expect-error-line2 Type '0' | '1'
  // @skjs-expect-error-line3 is not compatible with type '0'
  // @skjs-expect-error-line4 Value '1' is missing
  update<0, { value: number }>("counter", [[1, [{ value: 1 }]]]);
}
