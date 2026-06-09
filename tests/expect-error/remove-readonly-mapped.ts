// Mapped type (not yet supported, but -readonly is valid here)
// @skjs-expect-error Indexed access types ('T[K]') are not yet supported by SKJS
type Mutable<T> = { -readonly [K in keyof T]: T[K] };
