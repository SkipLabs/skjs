// prettier-ignore
// A \u escape needs four hex digits (or \u{H..}). tsc rejects a truncated one
// (TS1125); skjs rejects it rather than storing an undecoded lexeme (#771). The
// \x sibling is pinned separately; this exercises the \u code path.
// @skjs-expect-error Hexadecimal digit expected
type T = "\u6";
