// Type predicates in function declarations — the return type `x is T` is
// syntactically boolean and should be accepted; only the narrowing effect is lost.
//
// Currently rejected; will be supported once TAIs → boolean.

// @skjs-expect-error Type predicates ('x is T') are not yet supported by SKJS
declare function isArray(value: unknown): value is unknown[];
