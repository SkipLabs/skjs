// In JavaScript -0 === 0, and TypeScript folds the literal type -0 into 0.
// The sign is applied after normalization via negateJSNumberLiteral, which
// collapses -0 to 0.

function negativeZeroValue(): void {
  const a: 0 = -0;
}

function negativeZeroType(): void {
  const a: -0 = 0;
}

// Both operands are the single value 0, so the comparison is always true.
function negativeZeroOverlap(x: -0, y: 0): boolean {
  // @skjs-expect-warning This comparison is always true because the operands always hold the same single value
  return x === y;
}
