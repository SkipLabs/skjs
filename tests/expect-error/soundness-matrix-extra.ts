function acceptsUnionObject(x: { a: number } | { b: number }): void {
  console.log(x);
}

function spreadFreshnessFallbackIsNotApplied(): void {
  const one: 1 = 1;
  let narrow: { a: 1 } = { a: one };
  // Spread carries an alias-bearing source; fresh fallback must not apply.
  // @skjs-expect-error Invalid call
  acceptsUnionObject({ ...narrow });
}
