// prettier-ignore
// Template-literal interpolation scanning must skip string literals, nested
// templates, comments, and backslash escapes inside the interpolation
// expression (#820). Pinned to the pre-fix behavior; the fix removes the
// annotations on the two false positives.

// An escaped ${ is literal text, not an interpolation.
function escapedDollarBrace(): string {
  // @skjs-expect-error Cannot find name
  return `\${x}`;
}

// A } (and a ${...} substring) inside a string argument is literal text.
function closeBraceInStringArg(): string {
  // @skjs-expect-error Cannot find name
  return `${"}${zzz}"}`;
}

// Regression guards: these already work and must keep working.
function realInterpolation(): string {
  return `a${1}b`;
}

function nestedTemplate(): string {
  return `${`x`}`;
}

// Control: an object-typed interpolation stays rejected (its object literal
// is parsed correctly either way).
function objectInterpolation(): string {
  // @skjs-expect-error Template literal expressions must be of type string, number, bigint, boolean, null, or undefined
  return `${ {a:1} }`;
}
