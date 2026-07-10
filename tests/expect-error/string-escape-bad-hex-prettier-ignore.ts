// prettier-ignore
// A \x escape needs exactly two hex digits. tsc rejects a truncated one
// (TS1125); skjs rejects it rather than storing an undecoded lexeme (#771).
// Pinned first to the buggy pre-fix behavior, which accepted the raw lexeme.
type T = "\x6";
