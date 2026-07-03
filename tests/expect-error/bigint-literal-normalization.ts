// Bigint literal types are normalized like number literals: underscores
// stripped, radix forms converted to decimal (exactly — bigints are
// arbitrary precision), and -0n folded to 0n.

function bigintUnderscore(): void {
  const a: 1000n = 1_000n;
}

function bigintHex(): void {
  const a: 16n = 0x10n;
}

// Bigint has no negative zero: -0n collapses to 0n at the negation site.
function bigintNegativeZero(): void {
  const a: 0n = -0n;
}

function bigintNegativeUnderscore(): void {
  const a: -1000n = -1_000n;
}

// A genuine value mismatch must stay an error after normalization.
function bigintNegativeControl(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const a: 1001n = 1_000n;
}
