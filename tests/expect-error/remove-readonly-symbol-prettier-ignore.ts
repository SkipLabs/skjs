declare const sym: unique symbol;
// @skjs-expect-error '-readonly' modifier can only appear in mapped types
// @skjs-expect-error TODO symbol
type Qux = { -readonly [sym]: number; };
