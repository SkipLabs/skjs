// A `.` that a digit follows begins a NumericLiteral, so the integer part may be
// omitted: `.5` is `0.5`. The literal type is the normalized value, which is
// what these annotations pin -- lexing it as one token is only half the job.
//
// Prettier-exempt on purpose: prettier rewrites `.5` to `0.5`, which would
// leave every case here testing the spelling it is meant to contrast with.

function half(): 0.5 {
  return 0.5;
}

function leadingDot(): 0.5 {
  return .5;
}

function leadingDotTrailingZero(): 0.5 {
  return .50;
}

function leadingDotExponent(): 500 {
  return .5e3;
}

function leadingDotSignedExponent(): 500 {
  return .5e+3;
}

// The neighbours a leading-dot number must not disturb: a trailing dot is still
// the same number, and `...` is still a spread.
function trailingDot(): 5 {
  return 5.;
}

function spread(...xs: number[]): number {
  return xs.length;
}

function usesSpread(): number {
  return spread(...[1, 2]);
}
