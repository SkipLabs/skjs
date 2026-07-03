// Bigint literal types are compared textually: getBigInt does not normalize
// underscores, radix prefixes, or signs the way getNumber now does.

// FIXME: tsc accepts: 1_000n and 1000n are the same bigint value
function bigintUnderscore(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const a: 1000n = 1_000n;
}

// FIXME: tsc accepts: 0x10n is 16n
function bigintHex(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const a: 16n = 0x10n;
}

// FIXME: tsc accepts: -0n is 0n (bigint has no negative zero)
function bigintNegativeZero(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const a: 0n = -0n;
}

// FIXME: tsc accepts: -1_000n is -1000n
function bigintNegativeUnderscore(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const a: -1000n = -1_000n;
}

// A genuine value mismatch must stay an error after normalization.
function bigintNegativeControl(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const a: 1001n = 1_000n;
}
