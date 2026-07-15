// Template literal types, pinned at the pre-support state: every form below is
// rejected today with the same blanket error. The cases are grouped by the
// reduction rule they exercise, so that later work flips exactly the reducible
// ones and leaves the irreducible ones rejected.

// --- Templates with no live hole: reduce to a single string literal type ---

// @skjs-expect-error Template literal types are not yet supported by SKJS
type NoSubstitution = `abc`;

// @skjs-expect-error Template literal types are not yet supported by SKJS
type LiteralHole = `a${"b"}c`;

// Escapes are cooked, so this is the type "a" (as in a quoted string literal).
// @skjs-expect-error Template literal types are not yet supported by SKJS
type CookedEscape = `\x61`;

// A number hole stringifies with ECMAScript semantics: this is "1e+21".
// @skjs-expect-error Template literal types are not yet supported by SKJS
type NumberLiteralHole = `${1e21}`;

// A bigint hole drops the `n` suffix: this is "1".
// @skjs-expect-error Template literal types are not yet supported by SKJS
type BigIntLiteralHole = `${1n}`;

// @skjs-expect-error Template literal types are not yet supported by SKJS
type Nested = `a${`b${"c"}d`}e`;

// --- Holes over finite types: distribute into a literal union ---

// @skjs-expect-error Template literal types are not yet supported by SKJS
type UnionHole = `${"a" | "b"}-${"x" | "y"}`;

// @skjs-expect-error Template literal types are not yet supported by SKJS
type BooleanHole = `${boolean}`;

// @skjs-expect-error Template literal types are not yet supported by SKJS
type NullHole = `${null}`;

// @skjs-expect-error Template literal types are not yet supported by SKJS
type UndefinedHole = `${undefined}`;

// `never` absorbs: the whole template is never.
// @skjs-expect-error Template literal types are not yet supported by SKJS
type NeverHole = `x${never}y`;

// --- Degenerate string holes: reduce to the `string` primitive itself ---

// @skjs-expect-error Template literal types are not yet supported by SKJS
type BareString = `${string}`;

// @skjs-expect-error Template literal types are not yet supported by SKJS
type TwoBareStrings = `${string}${string}`;

// --- Irreducible holes: an infinite, partial set of strings ---

// @skjs-expect-error Template literal types are not yet supported by SKJS
type Prefixed = `a${string}b`;

// @skjs-expect-error Template literal types are not yet supported by SKJS
type NumberHole = `${number}`;

// --- Holes whose type may not be interpolated at all ---

// @skjs-expect-error Template literal types are not yet supported by SKJS
type ObjectHole = `${object}`;

// @skjs-expect-error Template literal types are not yet supported by SKJS
type SymbolHole = `${symbol}`;

// @skjs-expect-error Template literal types are not yet supported by SKJS
type UnknownHole = `${unknown}`;

// @skjs-expect-error Template literal types are not yet supported by SKJS
type VoidHole = `${void}`;

// --- Positions that stress the parser rather than the reduction ---

// A template type inside a parenthesized function type: the parser's only blind
// token-scanning lookahead (isTypeFunParams) must skip the template whole.
// @skjs-expect-error Template literal types are not yet supported by SKJS
type InFunctionParams = (x: `a${string}b`) => void;

// An arbitrary (non-stringifiable) type parses inside a hole; rejecting it is a
// typecheck obligation, not a syntactic one.
// @skjs-expect-error Template literal types are not yet supported by SKJS
type FunctionTypeHole = `${(q: string) => void}`;
