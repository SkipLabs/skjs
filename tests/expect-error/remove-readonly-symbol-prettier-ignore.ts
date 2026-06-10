declare const sym: unique symbol;
// @skjs-expect-error '-readonly' modifier can only appear in a mapped type
type Qux = { -readonly [sym]: number; };
