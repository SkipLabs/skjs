// @skjs-expect-error Unexpected modifier '-readonly' on an object literal method
type Baz = { -readonly foo(): void; };
