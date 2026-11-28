// Mapped type with -readonly is valid syntax and expands on tuples/arrays.
type Mutable<T> = { -readonly [K in keyof T]: T[K] };
