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

// @skjs-expect-error Enum instantiation is not yet supported by SKJS
function memberToEnum(): E {
  return E.A;
}

function memberToNumber(): number {
  return E.A;
}

function memberToItsLiteral(): 0 {
  return E.A;
}

function memberToWrongLiteral(): 1 {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
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

// @skjs-expect-error Enum instantiation is not yet supported by SKJS
function crossEnumMember(): F {
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
  return Offset.B;
}

enum Negative {
  A = -1,
  B,
}

function negativeMember(): -1 {
  return Negative.A;
}

function negativeAutoIncrement(): 0 {
  return Negative.B;
}

function assignToMember(): void {
  // @skjs-expect-error Type is not assignable to the assignment target's type
  E.A = 0;
}

function reverseLookup(): "A" {
  return E[0];
}

function reverseLookupUnion(i: 0 | 1): "A" | "B" {
  return E[i];
}

function reverseLookupNonLiteral(n: number): string {
  // @skjs-expect-error Cannot index this type with a non-literal key: it has no index signature
  return E[n];
}

function forwardByName(): 0 {
  return E["A"];
}

function keyOfEnumObject(): keyof typeof E {
  return "A";
}

function typeofEnumObject(o: typeof E): 0 {
  return o.A;
}

function enumObjectValue(): { readonly A: 0 } {
  return E;
}

// @skjs-expect-error Enum instantiation is not yet supported by SKJS
function narrowByEquality(x: E): 1 {
  if (x === E.A) {
    return 1;
  }
  return x;
}

// @skjs-expect-error Enum instantiation is not yet supported by SKJS
function switchOverEnum(x: E): number {
  switch (x) {
    // @skjs-expect-error A switch case expression must be a plain value, but this one may throw.
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
  // @skjs-expect-error This expression is not constructable
  new E();
}

function instanceofEnum(x: unknown): boolean {
  // @skjs-expect-error The right-hand side of an 'instanceof' expression must be either of type 'any', a class, function, or other type assignable to the 'Function' interface type, or an object type with a 'Symbol.hasInstance' method.
  return x instanceof E;
}

enum Flags {
  R = 1,
  W = 2,
}

// @skjs-expect-error Enum instantiation is not yet supported by SKJS
function bitFlagsCombination(): Flags {
  return Flags.R | Flags.W;
}

// @skjs-expect-error Cannot find type 'E.C'
function unknownMemberType(x: E.C): void {
  void x;
}
