// Type predicates in function declarations — the return type `x is T` is
// syntactically boolean and should be accepted; only the narrowing effect is
// lost.

declare function isArray(value: unknown): value is unknown[];

// The target type `T` is not validated yet: a nonexistent type is currently
// accepted too.
declare function isFoo(value: unknown): value is NonExistentType;
