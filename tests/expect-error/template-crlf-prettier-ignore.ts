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
  return x;
}

function crlfInExpr(): "a\nb" {
  return `a
b`;
}

// --- A lone raw CR is also the value <LF> ---

function loneCrInType(x: `ab`): "a\nb" {
  return x;
}

// --- Every line terminator in the text normalizes, not just the first ---

function severalTerminators(x: `a
b
c`): "a\nb\nc" {
  return x;
}

// A CR and a CRLF are two terminators, so this is two line feeds -- which also
// pins the order: the CRLF has to be taken before the lone CR.
function crThenCrlf(x: `a
b`): "a\n\nb" {
  return x;
}

// --- <LS> and <PS> are line terminators whose TV is themselves ---

// Normalizing these would be the natural over-generalization: ECMA-262 lists
// them as LineTerminators right beside <CR> and <LF>, but sec 12.9.6 gives each
// a TV of itself. Their bytes are as load-bearing here as the CRs above.
function lineSeparatorKeepsItself(x: `a b`): "a\u2028b" {
  return x;
}

function paragraphSeparatorKeepsItself(x: `a b`): "a\u2029b" {
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
