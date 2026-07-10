// prettier-ignore
// A \u{H..} code point escape must be <= 0x10FFFF. tsc rejects a larger one
// (TS1198); skjs rejects it rather than storing an undecoded lexeme (#771).
// Pinned first to the buggy pre-fix behavior, which accepted the raw lexeme.
type T = "\u{110000}";
