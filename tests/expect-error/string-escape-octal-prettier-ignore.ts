// prettier-ignore
// A legacy octal escape sequence. tsc rejects these under --strict (TS1487);
// leaving them undecoded is unsound (issue #771), so skjs rejects them too.
// Pinned first to the buggy pre-fix behavior, which accepted the raw lexeme.
type T = "\1";
