// Type predicates in function declarations — the return type `x is T` is
// syntactically boolean and should be accepted; only the narrowing effect is
// lost.

declare function isArray(value: unknown): value is unknown[];

// The target type `T` is validated like any other type reference.
// @skjs-expect-error Cannot find type 'NonExistentType'
declare function isFoo(value: unknown): value is NonExistentType;
