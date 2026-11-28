// Strict comparison overlap checking for `typeof` expressions.
//
// `typeof expr` keeps its wide `string` type in value position (no more
// permissive than tsc), while strict equality/inequality (`===` / `!==`)
// narrows each `typeof expr` operand to the set of runtime `typeof` tags
// reachable by `expr`'s type and runs the standard SKJS2040 / SKJS2074 check.

class BoxedClass {
  x: number = 1;
}

// Repro from the motivating case: `x` has type `number | string` (narrowed to
// `number` by `= 1`), so `typeof x === "boolean"` is provably always false.
function branchNarrowingInsideBodyStillReachesAfter(cond: boolean): number {
  let x: number | string = 1;
  if (cond) {
    // @skjs-expect-warning This comparison is always false because the operand types do not overlap
    if (typeof x === "boolean") {
      const n: never = x;
    }
    x = 2;
  } else {
    return 0;
  }
  return x;
}

// Basic primitive mismatches
function primitiveMismatches(x: number | string): boolean {
  // @skjs-expect-warning This comparison is always false because the operand types do not overlap
  const a = typeof x === "boolean";
  // @skjs-expect-warning This comparison is always true because the operand types do not overlap
  const b = typeof x !== "boolean";
  // @skjs-expect-warning This comparison is always false because the operand types do not overlap
  const c = "object" === typeof x;
  // @skjs-expect-warning This comparison is always false because the operand types do not overlap
  const d = typeof x === "undefined";
  // @skjs-expect-warning This comparison is always false because the operand types do not overlap
  const e = typeof x === "symbol";
  // @skjs-expect-warning This comparison is always false because the operand types do not overlap
  const f = typeof x === "bigint";
  // @skjs-expect-warning This comparison is always false because the operand types do not overlap
  const g = typeof x === "function";
  return a && b && c && d && e && f && g;
}

// Comparing two typeof expressions with disjoint operand types
function typeofVsTypeof(a: number, b: string): boolean {
  // @skjs-expect-warning This comparison is always false because the operand types do not overlap
  return typeof a === typeof b;
}

// Comparing two typeof expressions that hold the same single runtime tag
function typeofVsTypeofSameSingleton(a: number, b: number): boolean {
  // @skjs-expect-warning This comparison is always true because the operands always hold the same single value
  return typeof a === typeof b;
}

// Comparing two typeof expressions that can overlap (not singleton) must stay silent
function typeofVsTypeofOverlapping(
  a: number | string,
  b: string | boolean,
): boolean {
  return typeof a === typeof b;
}

// Comparing typeof to a typed string union variable (non-literal RHS)
function typeofVsStringUnion(
  x: number,
  tag: "boolean" | "symbol",
  wide: "number" | "boolean",
): boolean {
  // @skjs-expect-warning This comparison is always false because the operand types do not overlap
  const disjoint = typeof x === tag;
  const overlapping = typeof x === wide;
  return disjoint && overlapping;
}

// Invalid typeof tag outside an `if` condition (not reached by evalTypeofEquality)
function invalidTagOutsideIf(x: number | string): boolean {
  // @skjs-expect-error 'array' is not a valid operand for a 'typeof' comparison
  return typeof x === "array";
}

// Valid overlapping checks must stay silent
function validChecks(
  u: number | string | boolean | bigint | symbol | undefined | null,
): number {
  if (typeof u === "number") {
    return 1;
  } else if (typeof u === "string") {
    return 2;
  } else if (typeof u === "boolean") {
    return 3;
  } else if (typeof u === "bigint") {
    return 4;
  } else if (typeof u === "symbol") {
    return 5;
  } else if (typeof u === "undefined") {
    return 6;
  } else if (typeof u === "object") {
    return 7;
  }
  return 0;
}

// `null` has typeof "object" at runtime
function nullTypeof(x: null): boolean {
  const ok = typeof x === "object";
  // @skjs-expect-warning This comparison is always false because the operand types do not overlap
  const bad = typeof x === "undefined";
  return ok && bad;
}

// Class instances are non-callable objects: typeof is "object", never "function" or primitive
function classInstanceTypeof(c: BoxedClass): boolean {
  const okObj = typeof c === "object";
  // @skjs-expect-warning This comparison is always false because the operand types do not overlap
  const badFn = typeof c === "function";
  // @skjs-expect-warning This comparison is always false because the operand types do not overlap
  const badNum = typeof c === "number";
  return okObj && badFn && badNum;
}

// Plain object literals and arrays are definitely non-callable objects
function arrayAndLiteralTypeof(arr: number[]): boolean {
  const obj = { a: 1 };
  // @skjs-expect-warning This comparison is always false because the operand types do not overlap
  const badArrFn = typeof arr === "function";
  // @skjs-expect-warning This comparison is always false because the operand types do not overlap
  const badArrStr = typeof arr === "string";
  // @skjs-expect-warning This comparison is always false because the operand types do not overlap
  const badObjFn = typeof obj === "function";
  const okArr = typeof arr === "object";
  return badArrFn && badArrStr && badObjFn && okArr;
}

// Callable / constructible types are definitely typeof "function", never "object"
function callableAndCtorTypeof(
  fn: () => void,
  ctor: typeof BoxedClass,
): boolean {
  const okFn = typeof fn === "function";
  // @skjs-expect-warning This comparison is always false because the operand types do not overlap
  const badFnObj = typeof fn === "object";
  const okCtor = typeof ctor === "function";
  // @skjs-expect-warning This comparison is always false because the operand types do not overlap
  const badCtorObj = typeof ctor === "object";
  return okFn && badFnObj && okCtor && badCtorObj;
}

// Structural object types with unknown callability can be "object" OR "function"
// (e.g. a function carrying extra properties), so neither "object" nor "function" warns,
// while an incompatible primitive like "number" DOES warn.
function structuralObjectTypeof(o: { a: number }): boolean {
  const maybeObj = typeof o === "object";
  const maybeFn = typeof o === "function";
  // @skjs-expect-warning This comparison is always false because the operand types do not overlap
  const neverNum = typeof o === "number";
  return maybeObj && maybeFn && neverNum;
}

// Soundness with boxed primitives: `{}` and `{ length: number }` can be inhabited
// by primitive values (`"abc"` satisfies `{ length: number }`, any non-nullish
// primitive satisfies `{}`), so those checks MUST stay silent.
function boxedPrimitiveSoundness(
  empty: {},
  hasLength: { length: number },
  hasToFixed: { toFixed(digits?: number): string },
): boolean {
  const eStr = typeof empty === "string";
  const eNum = typeof empty === "number";
  const eBool = typeof empty === "boolean";
  const eBig = typeof empty === "bigint";
  const eSym = typeof empty === "symbol";
  const eObj = typeof empty === "object";
  const eFn = typeof empty === "function";
  // `undefined` and `null` do not satisfy `{}`:
  // @skjs-expect-warning This comparison is always false because the operand types do not overlap
  const eUndef = typeof empty === "undefined";

  // `"hi"` has `.length: number`, so `"string"` is possible; `"number"` is not.
  const lStr = typeof hasLength === "string";
  // @skjs-expect-warning This comparison is always false because the operand types do not overlap
  const lNum = typeof hasLength === "number";

  // `1` has `.toFixed()`, so `"number"` is possible; `"boolean"` is not.
  const fNum = typeof hasToFixed === "number";
  // @skjs-expect-warning This comparison is always false because the operand types do not overlap
  const fBool = typeof hasToFixed === "boolean";

  return (
    eStr &&
    eNum &&
    eBool &&
    eBig &&
    eSym &&
    eObj &&
    eFn &&
    eUndef &&
    lStr &&
    lNum &&
    fNum &&
    fBool
  );
}

// `unknown`, unconstrained type parameters, and `never` must stay silent.
function topAndBottomTypeof<T>(u: unknown, t: T, n: never): boolean {
  const a = typeof u === "boolean";
  const b = typeof t === "boolean";
  const c = typeof n === "boolean";
  return a && b && c;
}

// Constrained type parameter: checked through its constraint.
function constrainedTypeParam<T extends number | string>(x: T): boolean {
  const ok = typeof x === "number";
  // @skjs-expect-warning This comparison is always false because the operand types do not overlap
  const bad = typeof x === "boolean";
  return ok && bad;
}

// `typeof` in value position must NOT become more permissive than tsc.
function typeofValuePositionStillWide(x: number): string {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const tag: "number" = typeof x;
  return tag;
}

// Invalid typeof tag inside `if`: keeps TS2367 without doubling up with SKJS2040.
function invalidTagInIfNoDuplicate(x: number | string): number {
  // @skjs-expect-error 'array' is not a valid operand for a 'typeof' comparison
  if (typeof x === "array") {
    return 1;
  }
  return 0;
}

// Narrowed last-branch re-check stays quiet (literal RHS exempts SKJS2074).
function narrowedLastBranchRecheck(x: number | string): number {
  if (typeof x === "number") {
    return x;
  } else if (typeof x === "string") {
    return x.length;
  }
  return 0;
}
