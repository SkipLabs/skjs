// @skjs-expect-error Unexpected modifier on object literal method: -readonly
type Baz = { -readonly foo(): void; };
