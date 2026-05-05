// Mapped type (not yet supported, but -readonly is valid here)
// @skjs-expect-error TODO TAGet
type Mutable<T> = { -readonly [K in keyof T]: T[K] };
