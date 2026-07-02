// Type predicates in function declarations — the return type `x is T` is
// syntactically boolean and should be accepted; only the narrowing effect is
// lost.

declare function isArray(value: unknown): value is unknown[];

// The target type `T` is validated like any other type reference.
// @skjs-expect-error Cannot find type 'NonExistentType'
declare function isFoo(value: unknown): value is NonExistentType;

// The subject must name an actual parameter of the enclosing function.
// @skjs-expect-error A type predicate's subject must be a parameter of the enclosing function, or 'this'
declare function isBar(value: unknown): valeu is string;
