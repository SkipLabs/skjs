// Type predicates in function declarations — the return type `x is T` is
// syntactically boolean and should be accepted; only the narrowing effect is lost.
//
// Currently rejected; will be supported once TAIs → boolean.

declare function isArray(value: unknown): value is unknown[];
