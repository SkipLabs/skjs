// Spread elements in an array literal under `as const` (issue #957): a spread
// of a tuple splices the tuple's element types into the resulting readonly
// tuple, e.g. `[...xs, 3] as const` with `xs: readonly [1, 2]` is
// `readonly [1, 2, 3]`. A spread of a non-tuple value has no fixed readonly
// tuple type (tsc gives it a variadic tuple like `readonly [...T[], 3]`, which
// SKJS cannot express), so it stays unsupported.
//
// The cases live inside functions because a top-level `const` must have a
// primitive type in SKJS. In a most-precise (const) context SKJS reports each
// `as const` as unnecessary (a warning, not an error; see #951).

function spreadTupleAtEnd(): void {
  // @skjs-expect-warning This 'as const' is unnecessary
  const xs = [1, 2] as const;
  // @skjs-expect-warning This 'as const' is unnecessary
  // @skjs-expect-error A 'const' assertion can only be applied to a string, number, boolean, array, or object literal
  const t = [...xs, 3] as const;
}

function spreadTupleInMiddle(): void {
  // @skjs-expect-warning This 'as const' is unnecessary
  const xs = [1, 2] as const;
  // @skjs-expect-warning This 'as const' is unnecessary
  // @skjs-expect-error A 'const' assertion can only be applied to a string, number, boolean, array, or object literal
  const t = [0, ...xs, "a"] as const;
}

function spreadNonTuple(arr: number[]): void {
  // @skjs-expect-warning This 'as const' is unnecessary
  // @skjs-expect-error A 'const' assertion can only be applied to a string, number, boolean, array, or object literal
  const u = [...arr, 3] as const;
}
