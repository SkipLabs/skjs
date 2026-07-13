// prettier-ignore
// String literal types decode ECMAScript escape sequences, so two spellings
// of the same string denote the same literal type (issue #771): each escaped
// spelling below is legal against its plain equivalent. This file is
// prettier-ignored so the exact escape spellings are preserved (prettier
// rewrites escapes such as "a" to "a").

function hexEscape(): void {
  const a: "a" = "\x61";
}

function unicodeEscape(): void {
  const a: "a" = "\u0061";
}

function unicodeCodePointEscape(): void {
  const a: "a" = "\u{61}";
}

function namedAndHexAgree(): void {
  // \n and \x0a are both U+000A.
  const a: "\n" = "\x0a";
}

function nulEscape(): void {
  // \0 and \x00 are both U+0000 (and non-empty, hence truthy).
  const a: "\0" = "\x00";
}

function nonEscapeCharacter(): void {
  // \a is a NonEscapeCharacter: its value is the character itself, "a".
  const a: "a" = "\a";
}

function escapedQuote(): void {
  const a: '"' = "\"";
}

function escapedBackslash(): void {
  const a: "\\" = "\x5c";
}

function surrogatePairEscape(): void {
  // A \uHHHH high+low surrogate pair denotes one astral code point: this pair
  // is U+1F600, the same code point as the source character 😀.
  const a: "😀" = "\uD83D\uDE00";
}

function tabEscape(): void {
  // \t and \x09 are both U+0009.
  const a: "\t" = "\x09";
}

function backspaceEscape(): void {
  // \b and \x08 are both U+0008.
  const a: "\b" = "\x08";
}

// Negative control: genuinely distinct values stay a type error after decoding.
function distinctValuesStillError(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const a: "a" = "\x62";
}
