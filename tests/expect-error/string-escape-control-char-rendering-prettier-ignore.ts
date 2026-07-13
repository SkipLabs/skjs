// prettier-ignore
// Decoded control characters must be re-escaped when a literal type is
// rendered in a diagnostic (appendControlEscape). A raw newline in a field
// name previously reached TypePp::out and crashed (issue #771); these cases
// pin the escaped rendering so a regression is caught.

// renderPrimLiteral: a decoded newline value renders as \n, not a raw newline.
function newlineValueRenders(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  // @skjs-expect-error-line2 Type '"\n"'
  const a: "x" = "\n";
}

// renderPrimLiteral: a decoded NUL value renders as \0.
function nulValueRenders(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  // @skjs-expect-error-line2 Type '"\0"'
  const a: "x" = "\0";
}

// escapeName: a field name holding a decoded newline renders escaped (this is
// the path that previously crashed).
function newlineFieldNameRenders(x: { "a\nb": 0 }): { c: 0 } {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  // @skjs-expect-error-line2 Type '{ a\nb: 0; }'
  return x;
}
