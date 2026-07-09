enum G {
  A = ".".length,
  B = 4,
}

function computedMember(): number {
  return G.A;
}

function computedMemberIsNotItsRuntimeLiteral(): 1 {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return G.A;
}

function literalMemberInComputedEnum(): 4 {
  return G.B;
}

function computedEnumAcceptsAnyNumber(n: number): G {
  return n;
}

// A member with an unknown value could collide with any known one at
// runtime, so reverse-mapping fields are omitted entirely (tsc types G[4]
// as string).
function computedEnumHasNoReverseMapping(): string {
  // @skjs-expect-error Property '4' does not exist on this type
  return G[4];
}

enum H {
  A = ".".length,
  // @skjs-expect-error Enum member must have initializer
  B,
}

enum D {
  A,
  // @skjs-expect-error Duplicate identifier 'A'
  A = 2,
}

const enum CC {
  // @skjs-expect-error const enum member initializers must be constant expressions
  A = ".".length,
}

const enum CE {
  A,
  B,
}

function constEnumMember(): 0 {
  return CE.A;
}

enum R {
  A = 1,
  B = A,
  C = R.A,
}

function bareMemberReference(): 1 {
  return R.B;
}

function qualifiedMemberReference(): 1 {
  return R.C;
}

// tsc reports a forward member reference as TS2651; SKJS types the
// initializer as an expression, where B does not resolve.
enum Fwd {
  // @skjs-expect-error Cannot find name
  A = B,
  B = 1,
}

// FIXME: unsound — at runtime FwdQualified.B is undefined while A's
// initializer runs, so A is undefined, not a number; tsc rejects (TS2651).
enum FwdQualified {
  A = FwdQualified.B,
  B = 1,
}

enum Same {
  A = 0,
  B = 0,
}

// tsc types Same[0] as plain string; SKJS knows the runtime reverse entry
// is the last member with that value.
function duplicateValueReverse(): "B" {
  return Same[0];
}

enum Empty {}

// tsc treats an empty enum as number-like; in SKJS it has no members and
// therefore no values.
function emptyEnumIsUninhabited(x: Empty): never {
  return x;
}

enum Frac {
  A = 1.5,
  B,
}

function fractionalMember(): 1.5 {
  return Frac.A;
}

// FIXME: tsc folds fractional auto-increment precisely (1.5 + 1 = 2.5);
// SKJS over-approximates the member to number.
function fractionalAutoIncrement(): 2.5 {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return Frac.B;
}

enum Big {
  A = 9007199254740991,
  B,
}

function autoIncrementAtDoubleLimit(): 9007199254740992 {
  return Big.B;
}

enum BoolInit {
  // @skjs-expect-error Computed enum member values must be numbers
  A = true,
}

declare enum DE {
  A = 0,
  B,
}

function ambientInitializedMember(): 0 {
  return DE.A;
}

// Matches tsc: an uninitialized member of a (non-const) ambient enum is
// opaque; the declaration's implied auto-increment is not trusted.
function ambientUninitializedMemberIsOpaque(): 1 {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return DE.B;
}

declare const enum DCE {
  A,
  B,
}

function ambientConstEnumMember(): 0 {
  return DCE.A;
}
