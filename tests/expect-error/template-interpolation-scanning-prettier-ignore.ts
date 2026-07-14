// prettier-ignore
// Template-literal interpolation scanning skips string literals, nested
// templates, comments, and backslash escapes inside the interpolation
// expression, so braces / dollar-signs there are not miscounted (#820).

// An escaped ${ is literal text, not an interpolation: this template is the
// string literal type "${x}".
function escapedDollarBrace(): "${x}" {
  return `\${x}`;
}

// A '{' inside a string argument is not a structural brace.
function braceInStringArg(): string {
  return `${"{"}`;
}

// A '}' (and a ${...} substring) inside a string argument is literal text.
function closeBraceInStringArg(): string {
  return `${"}${zzz}"}`;
}

// A brace inside a string passed to a call.
function braceInCallArg(g: (s: string) => string): string {
  return `${g("{}")}`;
}

// A backtick inside a string argument.
function backtickInStringArg(): string {
  return `${"`"}`;
}

// A nested template that itself has an interpolation.
function nestedTemplateWithInterp(): string {
  return `${`${1}`}`;
}

// A block comment containing a brace inside the interpolation.
function commentWithBraceInInterp(a: number): string {
  return `${a /* } */ + 1}`;
}

// Regression guards for ordinary interpolation.
function realInterpolation(): string {
  return `a${1}b`;
}

function nestedTemplate(): string {
  return `${`x`}`;
}

// Control: an object-typed interpolation stays rejected (its object literal is
// parsed correctly either way).
function objectInterpolation(): string {
  // @skjs-expect-error Template literal expressions must be of type string, number, bigint, boolean, null, or undefined
  return `${ {a:1} }`;
}
