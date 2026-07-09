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
  A = 0x20000000000001,
}

function spelledBigCanonicalReverse(): string {
  // @skjs-expect-error Property '9007199254740994' does not exist on this type
  return SpelledBig[9007199254740994];
}

function spelledBigSpelledReverse(): "A" {
  // @skjs-expect-error Property '0x20000000000001' does not exist on this type
  return SpelledBig[0x20000000000001];
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
