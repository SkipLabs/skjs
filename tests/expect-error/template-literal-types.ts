// Template literal types. A template has no type of its own: it reduces either
// to the finite set of strings it can produce, or to `string`. The accepted
// cases below assert the reduced type in both directions, so they pin the exact
// type and not merely the absence of an error.

// --- Templates with no live hole: reduce to a single string literal type ---

type NoSubstitution = `abc`;
function noSubstitution(x: NoSubstitution): "abc" {
  const back: NoSubstitution = "abc";
  return x;
}

type LiteralHole = `a${"b"}c`;
function literalHole(x: LiteralHole): "abc" {
  const back: LiteralHole = "abc";
  return x;
}

// Escapes are cooked, so this is the type "a", as in a quoted string literal.
type CookedEscape = `\x61`;
function cookedEscape(x: CookedEscape): "a" {
  const back: CookedEscape = "a";
  return x;
}

// A number hole stringifies with ECMAScript semantics, not source text.
type NumberLiteralHole = `${1e21}`;
function numberLiteralHole(x: NumberLiteralHole): "1e+21" {
  const back: NumberLiteralHole = "1e+21";
  return x;
}

// A bigint hole drops the `n` suffix that the literal's spelling carries.
type BigIntLiteralHole = `${1n}`;
function bigIntLiteralHole(x: BigIntLiteralHole): "1" {
  const back: BigIntLiteralHole = "1";
  return x;
}

type Nested = `a${`b${"c"}d`}e`;
function nested(x: Nested): "abcde" {
  const back: Nested = "abcde";
  return x;
}

// --- Holes over finite types: distribute into a literal union ---

type UnionHole = `${"a" | "b"}-${"x" | "y"}`;
function unionHole(x: UnionHole): "a-x" | "a-y" | "b-x" | "b-y" {
  const back: UnionHole = "b-y";
  return x;
}

// The cross-product is exact: a string outside it is not assignable.
function unionHoleIsExact(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const outside: UnionHole = "a-z";
}

type BooleanHole = `${boolean}`;
function booleanHole(x: BooleanHole): "false" | "true" {
  const back: BooleanHole = "true";
  return x;
}

type NullHole = `${null}`;
function nullHole(x: NullHole): "null" {
  const back: NullHole = "null";
  return x;
}

type UndefinedHole = `${undefined}`;
function undefinedHole(x: UndefinedHole): "undefined" {
  const back: UndefinedHole = "undefined";
  return x;
}

// `never` has no values, so no string can be built: it absorbs the template.
type NeverHole = `x${never}y`;
function neverHole(x: NeverHole): never {
  return x;
}

// --- Degenerate string holes: reduce to the `string` primitive itself ---

type BareString = `${string}`;
function bareString(x: BareString): string {
  const back: BareString = "anything at all";
  return x;
}

type TwoBareStrings = `${string}${string}`;
function twoBareStrings(x: TwoBareStrings): string {
  const back: TwoBareStrings = "anything at all";
  return x;
}

// --- Irreducible holes: an infinite, partial set of strings ---

// @skjs-expect-error Template literal types are only supported when every interpolation has finitely many values, which this one does not
type Prefixed = `a${string}b`;

// @skjs-expect-error Template literal types are only supported when every interpolation has finitely many values, which this one does not
type NumberHole = `${number}`;

// @skjs-expect-error Template literal types are only supported when every interpolation has finitely many values, which this one does not
type BigIntHole = `${bigint}`;

// An abstract type parameter has no known values at the definition.
// @skjs-expect-error Template literal types are only supported when every interpolation has finitely many values, which this one does not
type Deferred<T extends string> = `a${T}b`;

// --- Holes whose type may not be interpolated at all ---

// @skjs-expect-error Type of this interpolation is not assignable to type 'string | number | bigint | boolean | null | undefined'
type ObjectHole = `${object}`;

// @skjs-expect-error Type of this interpolation is not assignable to type 'string | number | bigint | boolean | null | undefined'
type SymbolHole = `${symbol}`;

// @skjs-expect-error Type of this interpolation is not assignable to type 'string | number | bigint | boolean | null | undefined'
type UnknownHole = `${unknown}`;

// @skjs-expect-error Type of this interpolation is not assignable to type 'string | number | bigint | boolean | null | undefined'
type VoidHole = `${void}`;

// An arbitrary type parses in a hole; rejecting it is a typecheck obligation,
// not a syntactic one.
// @skjs-expect-error Type of this interpolation is not assignable to type 'string | number | bigint | boolean | null | undefined'
type FunctionTypeHole = `${(q: string) => void}`;

// A hole that may not be interpolated is reported even when another hole is
// irreducible: the constraint is checked before the template is reduced.
// @skjs-expect-error Type of this interpolation is not assignable to type 'string | number | bigint | boolean | null | undefined'
type NotStringifiableBeatsIrreducible = `${object}${number}`;

// --- Positions that stress the parser rather than the reduction ---

// A template type inside a parenthesized function type: the parser's only blind
// token-scanning lookahead (isTypeFunParams) must step over the template whole.
// @skjs-expect-error Template literal types are only supported when every interpolation has finitely many values, which this one does not
type InFunctionParams = (x: `a${string}b`) => void;

// The same, with a hole that itself contains parens, which blind paren counting
// would miscount. The template reduces, so the parameter type is exactly "a(b".
type ParensInHole = (x: `a${"("}b`) => void;
function parensInHole(f: ParensInHole): (x: "a(b") => void {
  return f;
}
