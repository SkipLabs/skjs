enum E {
  A,
  B,
}

enum F {
  A,
  B,
}

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

function literalToEnum(): E {
  return 0;
}

function literalToMemberType(): E.A {
  return 0;
}

function wrongLiteralToMemberType(): E.A {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return 1;
}

function outOfRangeLiteralToEnum(): E {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return 5;
}

// tsc accepts number -> enum (a deliberate hole kept for bit flags); SKJS
// rejects it: an arbitrary number is not in E's value set {0, 1}.
function numberToEnum(n: number): E {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return n;
}

function enumToNumber(x: E): number {
  return x;
}

function enumToMemberType(x: E): E.A {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x;
}

function memberTypeToEnum(x: E.B): E {
  return x;
}

// tsc rejects cross-enum assignment (TS2322, nominal); SKJS accepts it:
// sound, E and F share the runtime value set {0, 1}.
function crossEnumMember(): F {
  return E.A;
}

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

// tsc types reverse lookups as plain string; SKJS gives the precise
// member-name literal.
function reverseLookup(): "A" {
  return E[0];
}

function reverseLookupUnion(i: 0 | 1): "A" | "B" {
  return E[i];
}

// tsc accepts E[n] as string; the SKJS enum object has no number index
// signature, so reverse lookups need a literal (or member-union) key.
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

function narrowByEquality(x: E): 1 {
  if (x === E.A) {
    return 1;
  }
  return x;
}

function switchOverEnum(x: E): number {
  switch (x) {
    // @skjs-expect-error A switch case expression must be a plain value, but this one may throw.
    case E.A:
      return 0;
    default:
      return 1;
  }
}

function switchUnreachableCase(x: E): number {
  switch (x) {
    // @skjs-expect-warning This case is unreachable: its value is not in the switched type
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

// The bit-flags idiom only works in tsc through its number -> enum hole
// (Flags.R | Flags.W is typed number); type flag combinations as number.
function bitFlagsCombination(): Flags {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return Flags.R | Flags.W;
}

// @skjs-expect-error Namespace 'E' has no exported member 'C'
function unknownMemberType(x: E.C): void {
  void x;
}
