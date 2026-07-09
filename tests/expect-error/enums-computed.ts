// @skjs-expect-error enum is not supported by SKJS (ignored)
enum G {
  A = ".".length,
  B = 4,
}

function computedMember(): number {
  // @skjs-expect-error Cannot find name
  return G.A;
}

function computedMemberIsNotItsRuntimeLiteral(): 1 {
  // @skjs-expect-error Cannot find name
  return G.A;
}

function literalMemberInComputedEnum(): 4 {
  // @skjs-expect-error Cannot find name
  return G.B;
}

// @skjs-expect-error Enum instantiation is not yet supported by SKJS
function computedEnumAcceptsAnyNumber(n: number): G {
  return n;
}

function computedEnumHasNoReverseMapping(): string {
  // @skjs-expect-error Cannot find name
  return G[4];
}

// @skjs-expect-error enum is not supported by SKJS (ignored)
enum H {
  A = ".".length,
  B,
}

// @skjs-expect-error enum is not supported by SKJS (ignored)
enum D {
  A,
  A = 2,
}

// @skjs-expect-error enum is not supported by SKJS (ignored)
const enum CC {
  A = ".".length,
}

// @skjs-expect-error enum is not supported by SKJS (ignored)
const enum CE {
  A,
  B,
}

function constEnumMember(): 0 {
  // @skjs-expect-error Cannot find name
  return CE.A;
}

// @skjs-expect-error enum is not supported by SKJS (ignored)
enum R {
  A = 1,
  B = A,
  C = R.A,
}

function bareMemberReference(): 1 {
  // @skjs-expect-error Cannot find name
  return R.B;
}

function qualifiedMemberReference(): 1 {
  // @skjs-expect-error Cannot find name
  return R.C;
}

// @skjs-expect-error enum is not supported by SKJS (ignored)
enum Fwd {
  A = B,
  B = 1,
}

// @skjs-expect-error enum is not supported by SKJS (ignored)
enum Same {
  A = 0,
  B = 0,
}

function duplicateValueReverse(): "B" {
  // @skjs-expect-error Cannot find name
  return Same[0];
}

// @skjs-expect-error enum is not supported by SKJS (ignored)
enum Empty {}

// @skjs-expect-error Enum instantiation is not yet supported by SKJS
function emptyEnumIsUninhabited(x: Empty): never {
  return x;
}

// @skjs-expect-error enum is not supported by SKJS (ignored)
enum Frac {
  A = 1.5,
  B,
}

function fractionalMember(): 1.5 {
  // @skjs-expect-error Cannot find name
  return Frac.A;
}

function fractionalAutoIncrement(): 2.5 {
  // @skjs-expect-error Cannot find name
  return Frac.B;
}

// @skjs-expect-error enum is not supported by SKJS (ignored)
enum Big {
  A = 9007199254740991,
  B,
}

function autoIncrementAtDoubleLimit(): 9007199254740992 {
  // @skjs-expect-error Cannot find name
  return Big.B;
}

// @skjs-expect-error enum is not supported by SKJS (ignored)
enum BoolInit {
  A = true,
}

declare enum DE {
  A = 0,
  B,
}

function ambientInitializedMember(): 0 {
  // @skjs-expect-error Cannot find name
  return DE.A;
}

function ambientUninitializedMemberIsOpaque(): 1 {
  // @skjs-expect-error Cannot find name
  return DE.B;
}

declare const enum DCE {
  A,
  B,
}

function ambientConstEnumMember(): 0 {
  // @skjs-expect-error Cannot find name
  return DCE.A;
}
