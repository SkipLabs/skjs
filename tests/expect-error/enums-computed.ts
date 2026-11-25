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
  // @skjs-expect-error A member initializer in a enum declaration cannot reference members declared after it, including members defined in other enums
  A = B,
  B = 1,
}

// A qualified forward reference is rejected like tsc (TS2651): at runtime
// FwdQualified.B is undefined while A's initializer runs, so typing it as
// an expression (which sees the completed enum object) would be unsound.
enum FwdQualified {
  // @skjs-expect-error A member initializer in a enum declaration cannot reference members declared after it, including members defined in other enums
  A = FwdQualified.B,
  B = 1,
}

enum Same {
  A = 0,
  // @skjs-expect-warning Duplicate enum member value 0
  B = 0,
}

// tsc types Same[0] as plain string; SKJS knows the runtime reverse entry
// is the last member with that value.
function duplicateValueReverse(): "B" {
  // @skjs-expect-warning Ambiguous enum reverse mapping for value 0: it resolves to the last-declared member 'B'
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

// Auto-increment folds with double arithmetic, as in tsc: 1.5 + 1 = 2.5.
function fractionalAutoIncrement(): 2.5 {
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

declare enum AmbientComputed {
  // @skjs-expect-error In ambient enum declarations member initializer must be constant expression
  A = ".".length,
}

function ambientComputedMember(): number {
  return AmbientComputed.A;
}

declare const enum DCE {
  A,
  B,
}

function ambientConstEnumMember(): 0 {
  return DCE.A;
}

enum Shifted {
  R = 1,
  W = R << 1,
}

function shiftedMember(): 2 {
  return Shifted.W;
}

const enum ConstShifted {
  R = 1,
  W = R << 1,
}

function constShiftedMember(): 2 {
  return ConstShifted.W;
}

enum Arith {
  A = 1,
  B = A + 1,
}

function arithMember(): 2 {
  return Arith.B;
}

enum ComputedRef {
  A = ".".length,
  B = A,
}

function computedRefMember(): number {
  return ComputedRef.B;
}

enum StrConcat {
  A = "a" + "b",
}

function strConcatMember(): "ab" {
  return StrConcat.A;
}

enum FwdElement {
  // @skjs-expect-error A member initializer in a enum declaration cannot reference members declared after it, including members defined in other enums
  A = FwdElement["B"],
  B = 1,
}

enum CrossEarlier {
  A = Shifted.R,
}

function crossEarlierMember(): 1 {
  return CrossEarlier.A;
}

enum CrossLater {
  // @skjs-expect-error A member initializer in a enum declaration cannot reference members declared after it, including members defined in other enums
  A = CrossLaterTarget.B,
}

enum CrossLaterTarget {
  B = 1,
}

function crossLaterMember(): number {
  return CrossLater.A;
}

enum FracTail {
  A = 1.5,
  B,
  C,
}

function fracTailMember(): number {
  return FracTail.C;
}

enum BeyondDouble {
  A = 9007199254740992,
  B,
}

function beyondDoubleMember(): number {
  return BeyondDouble.B;
}

enum SpelledBig {
  // @skjs-expect-warning Number literal '0x20000000000001' is rounded to 9007199254740992 by IEEE-754 double precision
  A = 0x20000000000001,
}

function spelledBigCanonicalReverse(): string {
  // @skjs-expect-error Property '9007199254740994' does not exist on this type
  return SpelledBig[9007199254740994];
}

// 0x20000000000001 is the double 2^53, so its reverse-mapping key is
// "9007199254740992" whichever way it is spelled.
function spelledBigSpelledReverse(): "A" {
  // @skjs-expect-warning Number literal '0x20000000000001' is rounded to 9007199254740992 by IEEE-754 double precision
  return SpelledBig[0x20000000000001];
}

function spelledBigRoundedReverse(): "A" {
  return SpelledBig[9007199254740992];
}

function duplicateNameMemberType(): D.A {
  return D.A;
}

function switchDuplicateValueCase(x: Same): number {
  switch (x) {
    case Same.A:
      return 0;
    // @skjs-expect-warning This case is unreachable: its value is already handled by an earlier case
    case Same.B:
      return 1;
    // @skjs-expect-warning This 'default' case is unreachable: all values of the switched type are already handled
    default:
      return 2;
  }
}

declare namespace AmbientNS {
  enum NE {
    A,
  }
}

function ambientNamespaceEnumMember(x: AmbientNS.NE): 0 {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x;
}

// A bare name with no sibling member of that name resolves to the outer
// scope, like tsc.
const enumScopeOuter = 5;

enum ScopeOuterConst {
  A = enumScopeOuter,
  C = 2,
}

function scopeOuterConstMember(): number {
  return ScopeOuterConst.A;
}

function enumScopeFn(): number {
  return 1;
}

enum ScopeOuterFn {
  A = enumScopeFn(),
}

function scopeOuterFnMember(): number {
  return ScopeOuterFn.A;
}

// A bare reference to a later sibling reads undefined at runtime; the member
// scope shadows the outer scope, so this is a forward reference (tsc TS2651).
enum ScopeBareForward {
  // @skjs-expect-error A member initializer in a enum declaration cannot reference members declared after it, including members defined in other enums
  A = ScopeLater,
  ScopeLater = 1,
}

function scopeBareForwardMember(): number {
  return ScopeBareForward.A;
}

// The member `scopeShadowed` shadows the outer const, so A reads the
// not-yet-initialized member (undefined) at runtime, not the outer 5 (tsc
// TS2651).
const scopeShadowed = 5;

enum ScopeShadowSibling {
  // @skjs-expect-error A member initializer in a enum declaration cannot reference members declared after it, including members defined in other enums
  A = scopeShadowed,
  scopeShadowed = 1,
}

function scopeShadowMember(): number {
  return ScopeShadowSibling.A;
}

// A bare self reference reads undefined at runtime (tsc reports TS2565 here;
// SKJS reuses its forward-reference diagnostic).
enum ScopeSelfBare {
  // @skjs-expect-error A member initializer in a enum declaration cannot reference members declared after it, including members defined in other enums
  A = A,
}

function scopeSelfBareMember(): number {
  return ScopeSelfBare.A;
}

// A cyclic cross-enum reference: the syntactically-forward member (declared
// first, referencing a later enum) is rejected (tsc TS2651); the back edge
// reads an already-declared enum, so it is an untracked number, like tsc.
enum Cyclic1 {
  // @skjs-expect-error A member initializer in a enum declaration cannot reference members declared after it, including members defined in other enums
  A = Cyclic2.B,
}

enum Cyclic2 {
  B = Cyclic1.A,
}

function cyclic1Member(): number {
  return Cyclic1.A;
}

function cyclic2Member(): number {
  return Cyclic2.B;
}

// A later member reusing an earlier member's numeric value shadows its
// reverse mapping at runtime; warn at the declaration.
enum DupValue {
  A = 1,
  B = 2,
  // @skjs-expect-warning Duplicate enum member value 1
  C = 1,
}

function dupValueMember(): 1 {
  return DupValue.C;
}

enum NoDupValue {
  A = 1,
  B = 2,
}

function noDupValueMember(): 2 {
  return NoDupValue.B;
}

// Duplicate string values have no reverse mapping to shadow, so no warning.
enum DupStringValue {
  A = "x",
  B = "x",
}

function dupStringMember(): "x" {
  return DupStringValue.B;
}

// Infinity members have the runtime reverse-mapping keys "Infinity" and
// "-Infinity", whichever way the value is spelled (tsc types the access as
// plain string).
enum InfinityMembers {
  // @skjs-expect-warning Number literal '1e309' overflows to Infinity
  Pos = 1e309,
  // @skjs-expect-warning Number literal '1e309' overflows to Infinity
  Neg = -1e309,
}

function infinityReverse(): "Pos" {
  // @skjs-expect-warning Number literal '2e309' overflows to Infinity
  return InfinityMembers[2e309];
}

function negInfinityReverse(): "Neg" {
  // @skjs-expect-warning Number literal '1e309' overflows to Infinity
  return InfinityMembers[-1e309];
}

// Constant folding over doubles: tsc folds every arithmetic initializer to
// the literal of its double. A NaN result has no literal type.
enum FloatFold {
  Sum = 0.1 + 0.2,
  Product = 1.5 * 2,
  Quotient = 10 / 3,
  Remainder = 5.5 % 2,
  NegRemainder = -5.5 % 2,
  // @skjs-expect-warning Number literal '1e309' overflows to Infinity
  InfRemainder = 1e309 % 2,
  PastSafe = 2 ** 53 + 1,
  Overflow = 1e308 * 10,
  Cancel = 0.5 - 0.5,
  NegZero = -0.5 * 0,
  Or = 1.5 | 0,
  Shift = -2.7 >> 0,
  HugeOr = 1e300 | 0,
  Tilde = ~1.5,
  NotANumber = 0 / 0,
}

function floatFoldSum(): 0.30000000000000004 {
  return FloatFold.Sum;
}

function floatFoldProduct(): 3 {
  return FloatFold.Product;
}

function floatFoldQuotient(): 3.3333333333333335 {
  return FloatFold.Quotient;
}

function floatFoldRemainder(): 1.5 {
  return FloatFold.Remainder;
}

function floatFoldNegRemainder(): -1.5 {
  return FloatFold.NegRemainder;
}

// Infinity % 2 is NaN at runtime, so the member is an untracked number.
function floatFoldInfRemainder(): number {
  return FloatFold.InfRemainder;
}

function floatFoldInfRemainderNotLiteral(): 0 {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return FloatFold.InfRemainder;
}

function floatFoldPastSafe(): 9007199254740992 {
  return FloatFold.PastSafe;
}

// @skjs-expect-warning Number literal '1e309' overflows to Infinity
function floatFoldOverflow(): 1e309 {
  return FloatFold.Overflow;
}

function floatFoldCancel(): 0 {
  return FloatFold.Cancel;
}

function floatFoldNegZero(): 0 {
  return FloatFold.NegZero;
}

function floatFoldOr(): 1 {
  return FloatFold.Or;
}

function floatFoldShift(): -2 {
  return FloatFold.Shift;
}

function floatFoldHugeOr(): 0 {
  return FloatFold.HugeOr;
}

function floatFoldTilde(): -2 {
  return FloatFold.Tilde;
}

function floatFoldNaN(): number {
  return FloatFold.NotANumber;
}

// A zero divisor's name drops the sign of -0 (1 / -0 is -Infinity), so
// division by zero stays an untracked number.
enum ZeroDivisor {
  A = 1 / 0,
  B = 1 / (-0.5 * 0),
}

// @skjs-expect-warning Number literal '1e309' overflows to Infinity
function zeroDivisorPositive(): 1e309 {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return ZeroDivisor.A;
}

// @skjs-expect-warning Number literal '-1e309' overflows to -Infinity
function zeroDivisorNegative(): -1e309 {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return ZeroDivisor.B;
}

// String concatenation renders a number by its String() form.
enum FloatConcat {
  // @skjs-expect-warning Number literal '1e309' overflows to Infinity
  A = "s" + 1e309,
}

function floatConcatInfinity(): "sInfinity" {
  return FloatConcat.A;
}
