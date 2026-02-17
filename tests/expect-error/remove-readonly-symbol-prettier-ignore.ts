declare const sym: unique symbol;
// @skjs-expect-error '-readonly' modifier can only appear in mapped types
type Qux = { -readonly [sym]: number; };
