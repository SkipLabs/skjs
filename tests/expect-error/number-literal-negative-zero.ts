// In JavaScript -0 === 0, and TypeScript folds the literal type -0 into 0.
// SKJS prepends the sign after normalization, so the non-canonical literal
// "-0" escapes into the type system.

// FIXME: tsc accepts: -0 and 0 are the same literal type
function negativeZeroValue(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const a: 0 = -0;
}

// FIXME: tsc accepts: -0 and 0 are the same literal type
function negativeZeroType(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const a: -0 = 0;
}

// FIXME: -0 === 0 is true at runtime, so this comparison is always true
function negativeZeroOverlap(x: -0, y: 0): boolean {
  // @skjs-expect-warning This comparison is always false because the operand types do not overlap
  return x === y;
}
