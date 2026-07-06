// Strict comparison (===, !==) diagnostics: SKJS warns when the operands'
// value sets are provably disjoint (the comparison always has the same
// outcome). Reference types (objects, functions, promises) are never
// reported: a single value can inhabit both sides (width subtyping,
// never-returning functions, Promise<never>), even when tsc reports TS2367.

class Cat {
  meow: string = "";
}
class Dog {
  bark: string = "";
}
class Pet {
  name: string = "";
}
class Cat2 {
  meow: string = "";
}

// No warning: one value can be both a Cat and a Dog
// (`{ meow: "", bark: "" }` satisfies both shapes)
function classDisjoint(x: Cat, y: Dog): boolean {
  return x === y;
}

function classCounterExample(): boolean {
  const v = { meow: "", bark: "" };
  const x: Cat = v;
  const y: Dog = v;
  return x === y;
}

function classUnionOverlap(x: Cat | Pet, y: Dog | Pet): boolean {
  return x === y;
}

function sameShapeClasses(x: Cat, y: Cat2): boolean {
  return x === y;
}

function primDisjoint(x: number, y: string): boolean {
  // @skjs-expect-warning This comparison is always false because the operand types do not overlap
  return x === y;
}

function litDisjoint(x: 0 | 1, y: 2 | 3): boolean {
  // @skjs-expect-warning This comparison is always false because the operand types do not overlap
  return x === y;
}

function litOverlap(x: 0 | 1, y: 1 | 2): boolean {
  return x === y;
}

function strLitDisjoint(x: "a", y: "b"): boolean {
  // @skjs-expect-warning This comparison is always false because the operand types do not overlap
  return x === y;
}

function boolLitDisjoint(x: true, y: false): boolean {
  // @skjs-expect-warning This comparison is always false because the operand types do not overlap
  return x === y;
}

// No warning: both can be `{ a: 0, b: "" }`. tsc reports TS2367 here, but
// the claim "always false" would be wrong.
function objDisjoint(x: { a: number }, y: { b: string }): boolean {
  return x === y;
}

function objCounterExample(): boolean {
  const v = { a: 0, b: "" };
  const x: { a: number } = v;
  const y: { b: string } = v;
  return x === y;
}

// No warning: one value can satisfy both all-optional (weak) types
function weakObjects(x: { a?: number }, y: { b?: string }): boolean {
  return x === y;
}

function weakVsRequiredDisjoint(x: { a?: number }, y: { b: string }): boolean {
  return x === y;
}

// No value satisfies both (a shared field with disjoint types), but object
// comparisons are exempt for simplicity; tsc reports TS2367
function weakSharedConflict(x: { a?: number }, y: { a: string }): boolean {
  return x === y;
}

// null and undefined overlap nothing but themselves: a null check on an
// operand that can never be null is dead code. tsc does not report these.
function numVsNull(x: number, y: null): boolean {
  // @skjs-expect-warning This comparison is always false because the operand types do not overlap
  return x === y;
}

function undefVsNull(x: undefined, y: null): boolean {
  // @skjs-expect-warning This comparison is always false because the operand types do not overlap
  return x === y;
}

function nullCheckOnNonNullable(x: number | undefined): boolean {
  // @skjs-expect-warning This comparison is always false because the operand types do not overlap
  return x === null;
}

function definedCheckOnNonOptional(x: number): boolean {
  // @skjs-expect-warning This comparison is always true because the operand types do not overlap
  return x !== undefined;
}

// Inside a union, a null/undefined branch only overlaps the same kind
function nullInUnionVsString(x: number | null, y: string): boolean {
  // @skjs-expect-warning This comparison is always false because the operand types do not overlap
  return x === y;
}

function unitsInUnionsDisjoint(
  x: number | null,
  y: string | undefined,
): boolean {
  // @skjs-expect-warning This comparison is always false because the operand types do not overlap
  return x === y;
}

function nullBranchesOverlap(x: number | null, y: string | null): boolean {
  return x === y;
}

function unionVsWholeNull(x: number | undefined, y: null): boolean {
  // @skjs-expect-warning This comparison is always false because the operand types do not overlap
  return x === y;
}

// No warning: both can be `(): never => { throw ... }`. tsc reports TS2367.
function funDisjoint(f: () => number, g: () => string): boolean {
  return f === g;
}

function funCounterExample(): boolean {
  const h = (): never => {
    throw new Error("unreachable");
  };
  const f: () => number = h;
  const g: () => string = h;
  return f === g;
}

// No warning: both can be valid `Promise<never>` values. tsc reports TS2367.
function promiseDisjoint(p: Promise<number>, q: Promise<string>): boolean {
  return p === q;
}

function promiseCounterExample(p0: Promise<never>): boolean {
  const p: Promise<number> = p0;
  const q: Promise<string> = p0;
  return p === q;
}

// A promise is an object; promise-vs-object comparisons are not reported
function promiseVsObject(p: Promise<number>, o: { a: number }): boolean {
  return p === o;
}

function promiseVsNumber(p: Promise<number>, n: number): boolean {
  // @skjs-expect-warning This comparison is always false because the operand types do not overlap
  return p === n;
}

// A primitive overlaps an object type only through its boxed class
function primVsDisjointObject(x: number, y: { a: string }): boolean {
  // @skjs-expect-warning This comparison is always false because the operand types do not overlap
  return x === y;
}

function primVsBoxedShape(
  x: number,
  y: { toFixed(digits?: number): string },
): boolean {
  return x === y;
}

// No warning: a tuple value is an array at runtime
function tupleVsArray(t: [number], a: number[]): boolean {
  return t === a;
}

function bareTypeParam<T>(x: T, y: number): boolean {
  return x === y;
}

function constrainedTypeParam<T extends string>(x: T, y: number): boolean {
  // @skjs-expect-warning This comparison is always false because the operand types do not overlap
  return x === y;
}

function unknownOperand(x: unknown, y: number): boolean {
  return x === y;
}

// 1e3 and 1000 normalize to the same numeric literal, so this is always true.
function numericNotation(x: 1e3, y: 1000): boolean {
  // @skjs-expect-warning This comparison is always true because the operands always hold the same single value
  return x === y;
}

// FIXME: tsc reports TS2367 (`object` excludes primitives); SKJS lowers the
// `object` keyword to the empty object type, which `number` overlaps
function numberVsObjectKeyword(n: number, o: object): boolean {
  return n === o;
}

function strictInequalityDisjoint(x: 0, y: 1): boolean {
  // @skjs-expect-warning This comparison is always true because the operand types do not overlap
  return x !== y;
}

// Comparisons between identical singleton types always evaluate to the same
// result; TypeScript does not report these
function alwaysTrueUndefined(x: undefined, y: undefined): boolean {
  // @skjs-expect-warning This comparison is always true because the operands always hold the same single value
  return x === y;
}

function alwaysTrueNull(x: null, y: null): boolean {
  // @skjs-expect-warning This comparison is always true because the operands always hold the same single value
  return x === y;
}

function alwaysTrueString(x: "a", y: "a"): boolean {
  // @skjs-expect-warning This comparison is always true because the operands always hold the same single value
  return x === y;
}

function alwaysTrueNumber(x: 0, y: 0): boolean {
  // @skjs-expect-warning This comparison is always true because the operands always hold the same single value
  return x === y;
}

function alwaysTrueTrue(x: true, y: true): boolean {
  // @skjs-expect-warning This comparison is always true because the operands always hold the same single value
  return x === y;
}

function alwaysFalseInequality(x: "a", y: "a"): boolean {
  // @skjs-expect-warning This comparison is always false because the operands always hold the same single value
  return x !== y;
}

// Re-checking a narrowed discriminant against a literal is idiomatic and
// exempt from the always-true warning
function exhaustiveNarrowedCheck(x: "a" | "b"): string {
  if (x === "a") {
    return "first";
  } else if (x === "b") {
    return "second";
  }
  return "";
}

// Signed literals are exempt like unsigned ones
function negativeLiteralRecheck(x: 1 | -1): string {
  if (x === 1) {
    return "pos";
  } else if (x === -1) {
    return "neg";
  }
  return "";
}

// FIXME: the literal exemption is syntactic, so re-checking against a
// hoisted constant still warns where the inline literal would be exempt
const B = "b";
function namedConstantRecheck(x: "a" | "b"): string {
  if (x === "a") {
    return "first";
    // @skjs-expect-warning This comparison is always true because the operands always hold the same single value
  } else if (x === B) {
    return "second";
  }
  return "";
}

// The literal operand itself is exempt from the always-true warning
function singletonVsOwnLiteral(x: "a"): boolean {
  return x === "a";
}

function singletonVsWider(x: "a", y: string): boolean {
  return x === y;
}

function sameUnionNotSingleton(x: "a" | 0, y: "a" | 0): boolean {
  return x === y;
}
