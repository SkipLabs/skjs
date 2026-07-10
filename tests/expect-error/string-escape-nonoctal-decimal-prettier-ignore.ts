// prettier-ignore
// A NonOctalDecimalEscapeSequence (\8 or \9). tsc rejects these (TS1488);
// skjs rejects them rather than storing an undecoded lexeme (issue #771).
// @skjs-expect-error Escape sequence '\8' is not allowed
type T = "\8";
