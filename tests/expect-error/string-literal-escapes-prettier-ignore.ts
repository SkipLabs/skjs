// prettier-ignore
// String literal types decode ECMAScript escape sequences, so two spellings
// of the same string denote the same literal type (issue #771). For example
// "a" and "\x61" are one type, and an assignment between them is legal. This
// file is prettier-ignored so the exact escape spellings are preserved
// (prettier rewrites escapes such as "a" to "a").
//
// Pinned to the buggy pre-fix behavior, where each escaped spelling was stored
// as its raw source lexeme and therefore compared unequal to the plain
// spelling. The fix removes the annotations on the equivalence cases (they
// become legal); the mismatch control stays an error.

function hexEscape(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const a: "a" = "\x61";
}

function unicodeEscape(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const a: "a" = "\u0061";
}

function unicodeCodePointEscape(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const a: "a" = "\u{61}";
}

function namedAndHexAgree(): void {
  // \n and \x0a are both U+000A.
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const a: "\n" = "\x0a";
}

function nulEscape(): void {
  // \0 and \x00 are both U+0000 (and non-empty, hence truthy).
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const a: "\0" = "\x00";
}

function nonEscapeCharacter(): void {
  // \a is a NonEscapeCharacter: its value is the character itself, "a".
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const a: "a" = "\a";
}

function escapedQuote(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const a: '"' = "\"";
}

function escapedBackslash(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const a: "\\" = "\x5c";
}

function surrogatePairEscape(): void {
  // A \uHHHH high+low surrogate pair denotes one astral code point: this pair
  // is U+1F600, the same code point as the source character 😀.
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const a: "😀" = "\uD83D\uDE00";
}

// Negative control: genuinely distinct values stay a type error after decoding.
function distinctValuesStillError(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const a: "a" = "\x62";
}
