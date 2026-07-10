// prettier-ignore
// A \x escape needs exactly two hex digits. tsc rejects a truncated one
// (TS1125); skjs rejects it rather than storing an undecoded lexeme (#771).
// @skjs-expect-error Hexadecimal digit expected
type T = "\x6";
