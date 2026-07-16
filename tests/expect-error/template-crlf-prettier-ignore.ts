// Line terminators inside a template. ECMA-262 sec 12.9.6 gives a template's
// TV a normalized line terminator: a raw <CR><LF> or a lone <CR> in the source
// is the single character <LF> in the value. Only <LS>/<PS> keep themselves.
//
// The CRs below are real bytes, and they are the point of the test: the file is
// LF-terminated everywhere else, is prettier-exempt (prettier rewrites CRLF),
// and .gitattributes marks it -text so git cannot normalize it away. If a CR is
// ever lost, these cases silently pass while testing nothing.

// --- A raw CRLF is the value <LF> ---

function crlfInType(x: `a
b`): "a\nb" {
  // FIXME: cooked as \r\n, naming a string no runtime value produces.
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x;
}

function crlfInExpr(): "a\nb" {
  // FIXME: same, via a no-substitution template expression.
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return `a
b`;
}

// --- A lone raw CR is also the value <LF> ---

function loneCrInType(x: `ab`): "a\nb" {
  // FIXME: cooked as \r.
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x;
}

// --- An ESCAPE is not a raw line terminator and must NOT be normalized ---

function carriageReturnEscape(x: `a\rb`): "a\rb" {
  return x;
}

function hexEscapedCarriageReturn(x: `a\x0Db`): "a\rb" {
  return x;
}

// --- A line continuation over a CRLF is elided, as over an LF ---

function crlfLineContinuation(x: `a\
b`): "ab" {
  return x;
}
