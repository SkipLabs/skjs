// prettier-ignore
// A NonOctalDecimalEscapeSequence (\8 or \9). tsc rejects these (TS1488);
// skjs rejects them rather than storing an undecoded lexeme (issue #771).
// Pinned first to the buggy pre-fix behavior, which accepted the raw lexeme.
type T = "\8";
