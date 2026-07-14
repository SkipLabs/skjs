// prettier-ignore
// Edge cases for the inline template-interpolation parse (#820 refactor): all
// valid, all typed as string.

// Deeply nested templates with interpolations.
function deepNest(): string {
  return `a${`b${1}c`}d`;
}

// Adjacent interpolations produce empty string parts.
function emptyParts(a: number, b: number): string {
  return `${a}${b}`;
}

// A single interpolation with empty surrounding parts.
function loneInterp(a: number): string {
  return `${a}`;
}

// Whitespace and comments between the expression and its closing brace.
function commentBeforeBrace(a: number): string {
  return `x${ a /* c */ }y`;
}

// A nested template inside an interpolation, itself with an interpolation.
function nestedWithInterp(): string {
  return `${`${1}`}`;
}
