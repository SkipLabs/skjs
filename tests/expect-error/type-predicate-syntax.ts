// Type predicates in function declarations — the return type `x is T` is
// syntactically boolean and should be accepted; only the narrowing effect is
// lost.

declare function isArray(value: unknown): value is unknown[];

// The target type `T` is validated like any other type reference.
// @skjs-expect-error Cannot find type 'NonExistentType'
declare function isFoo(value: unknown): value is NonExistentType;

// The subject must name an actual parameter of the enclosing function; a
// typo is currently (wrongly) accepted since the subject is only
// shape-checked, not resolved.
declare function isBar(value: unknown): valeu is string;
