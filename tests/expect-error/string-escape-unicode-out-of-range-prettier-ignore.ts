// prettier-ignore
// A \u{H..} code point escape must be <= 0x10FFFF. tsc rejects a larger one
// (TS1198); skjs rejects it rather than storing an undecoded lexeme (#771).
// @skjs-expect-error An extended Unicode escape value must be between 0x0 and 0x10FFFF inclusive
type T = "\u{110000}";
