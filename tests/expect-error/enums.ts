// @skjs-expect-error Qualified name access ('A') is not yet supported by SKJS
// @skjs-expect-error Qualified name access ('B') is not yet supported by SKJS
// @skjs-expect-error Qualified name access ('C') is not yet supported by SKJS
enum E {
  A,
  B,
}

enum F {
  A,
  B,
}

function memberToEnum(): E {
  // @skjs-expect-error Cannot find name
  return E.A;
}

function memberToNumber(): number {
  // @skjs-expect-error Cannot find name
  return E.A;
}

function memberToItsLiteral(): 0 {
  // @skjs-expect-error Cannot find name
  return E.A;
}

function memberToWrongLiteral(): 1 {
  // @skjs-expect-error Cannot find name
  return E.A;
}

// @skjs-expect-error Enum instantiation is not yet supported by SKJS
function literalToEnum(): E {
  return 0;
}

// @skjs-expect-error Cannot find type 'E.A'
function literalToMemberType(): E.A {
  return 0;
}

// @skjs-expect-error Cannot find type 'E.A'
function wrongLiteralToMemberType(): E.A {
  return 1;
}

// @skjs-expect-error Enum instantiation is not yet supported by SKJS
function outOfRangeLiteralToEnum(): E {
  return 5;
}

// @skjs-expect-error Enum instantiation is not yet supported by SKJS
function numberToEnum(n: number): E {
  return n;
}

// @skjs-expect-error Enum instantiation is not yet supported by SKJS
function enumToNumber(x: E): number {
  return x;
}

// @skjs-expect-error Cannot find type 'E.A'
function enumToMemberType(x: E): E.A {
  return x;
}

// @skjs-expect-error Cannot find type 'E.B'
function memberTypeToEnum(x: E.B): E {
  return x;
}

function crossEnumMember(): F {
  // @skjs-expect-error Cannot find name
  return E.A;
}

// @skjs-expect-error Enum instantiation is not yet supported by SKJS
function crossEnumWhole(x: E): F {
  return x;
}

enum Offset {
  A = 5,
  B,
}

function autoIncrement(): 6 {
  // @skjs-expect-error Cannot find name
  return Offset.B;
}

enum Negative {
  A = -1,
  B,
}

function negativeMember(): -1 {
  // @skjs-expect-error Cannot find name
  return Negative.A;
}

function negativeAutoIncrement(): 0 {
  // @skjs-expect-error Cannot find name
  return Negative.B;
}

function assignToMember(): void {
  // @skjs-expect-error Cannot find name
  E.A = 0;
}

function reverseLookup(): "A" {
  // @skjs-expect-error Cannot find name
  return E[0];
}

function reverseLookupUnion(i: 0 | 1): "A" | "B" {
  // @skjs-expect-error Cannot find name
  return E[i];
}

function reverseLookupNonLiteral(n: number): string {
  // @skjs-expect-error Cannot find name
  return E[n];
}

function forwardByName(): 0 {
  // @skjs-expect-error Cannot find name
  return E["A"];
}

// @skjs-expect-error Cannot find name 'E'
function keyOfEnumObject(): keyof typeof E {
  return "A";
}

// @skjs-expect-error Cannot find name 'E'
function typeofEnumObject(o: typeof E): 0 {
  return o.A;
}

function enumObjectValue(): { readonly A: 0 } {
  // @skjs-expect-error Cannot find name
  return E;
}

// @skjs-expect-error Enum instantiation is not yet supported by SKJS
function narrowByEquality(x: E): 1 {
  if (x === E.A) {
    return 1;
  }
  return x;
}

function switchOverEnum(x: E): number {
  switch (x) {
    // @skjs-expect-error A switch case expression must be a plain value, but this one may throw.
    // @skjs-expect-error Cannot find name
    case E.A:
      return 0;
    default:
      return 1;
  }
}

// @skjs-expect-error Enum instantiation is not yet supported by SKJS
function switchUnreachableCase(x: E): number {
  switch (x) {
    case 5:
      return 0;
    default:
      return 1;
  }
}

function constructEnum(): void {
  // @skjs-expect-error Cannot find name
  new E();
}

function instanceofEnum(x: unknown): boolean {
  // @skjs-expect-error Cannot find name
  return x instanceof E;
}

enum Flags {
  R = 1,
  W = 2,
}

function bitFlagsCombination(): Flags {
  // @skjs-expect-error Cannot find name
  return Flags.R | Flags.W;
}

// @skjs-expect-error Cannot find type 'E.C'
function unknownMemberType(x: E.C): void {
  void x;
}
