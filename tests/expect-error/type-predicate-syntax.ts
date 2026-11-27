// Type predicates in declared function signatures: valid predicates are
// accepted, while malformed subjects and target types are rejected.

declare function isArray(value: unknown): value is unknown[];

// The target type `T` is validated like any other type reference.
// @skjs-expect-error Cannot find type 'NonExistentType'
declare function isFoo(value: unknown): value is NonExistentType;

// The subject must name an actual parameter of the enclosing function.
// @skjs-expect-error A type predicate's subject must be a parameter of the enclosing function, or 'this'
declare function isBar(value: unknown): valeu is string;

// A rest parameter cannot be the subject of a type predicate (TS1229).
// @skjs-expect-error A type predicate cannot reference a rest parameter
declare function isRest(...values: unknown[]): values is string[];
