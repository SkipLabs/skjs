// Tests for type refinement applied to global (module-level) variables.
// SKJS skips narrowing for non-local names because it would only be sound
// for truly immutable globals (readonly/declare const is not enough, since
// mutation through closures or aliases is still possible).
// Each test demonstrates that the narrowing does NOT apply: the original
// union type is retained in the branch that would otherwise be narrowed.

declare const gStr: string | null;
declare const gNum: number | undefined;
declare const gUnion: string | number;
declare const gBoolOrNull: boolean | null;
declare const gArrOrStr: number[] | string;
declare const gObj: { a?: number; kind?: "x" | "y" };
declare const gUnionObj: { a: number } | { b: string };
declare class MyCls {}
declare const gCls: MyCls | null;

// ============================================================
// 1. typeof narrowing
// ============================================================

function testTypeofString(): string {
  if (typeof gStr === "string") {
    // @skjs-expect-error Type of returned value is not assignable to the function's return type
    return gStr;
  }
  return "";
}

function testTypeofNumber(): number {
  if (typeof gUnion === "number") {
    // @skjs-expect-error Type of returned value is not assignable to the function's return type
    return gUnion;
  }
  return 0;
}

function testTypeofBoolean(): boolean {
  if (typeof gBoolOrNull === "boolean") {
    // @skjs-expect-error Type of returned value is not assignable to the function's return type
    return gBoolOrNull;
  }
  return false;
}

// ============================================================
// 2. null/undefined equality
// ============================================================

function testEqNull(): string {
  if (gStr === null) return "";
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return gStr;
}

function testNeqNull(): string {
  if (gStr !== null) {
    // @skjs-expect-error Type of returned value is not assignable to the function's return type
    return gStr;
  }
  return "";
}

function testEqUndefined(): number {
  if (gNum === undefined) return 0;
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return gNum;
}

function testNeqUndefined(): number {
  if (gNum !== undefined) {
    // @skjs-expect-error Type of returned value is not assignable to the function's return type
    return gNum;
  }
  return 0;
}

// ============================================================
// 3. Field equality narrowing (obj.field === constant)
// ============================================================

function testFieldEqConstant(): "x" {
  if (gObj.kind === "x") {
    // @skjs-expect-error Type of returned value is not assignable to the function's return type
    return gObj.kind;
  }
  return "x";
}

function testFieldNeqUndefined(): number {
  if (gObj.a !== undefined) {
    // @skjs-expect-error Type of returned value is not assignable to the function's return type
    return gObj.a;
  }
  return 0;
}

// ============================================================
// 4. Array.isArray
// ============================================================

function testIsArray(): number[] {
  if (Array.isArray(gArrOrStr)) {
    // @skjs-expect-error Type of returned value is not assignable to the function's return type
    return gArrOrStr;
  }
  return [];
}

// ============================================================
// 5. instanceof
// ============================================================

function testInstanceOf(): MyCls {
  if (gCls instanceof MyCls) {
    // @skjs-expect-error Type of returned value is not assignable to the function's return type
    return gCls;
  }
  return new MyCls();
}

// ============================================================
// 6. "key" in obj
// ============================================================

function testInOperator(): number {
  if ("a" in gUnionObj) {
    // @skjs-expect-error Property 'a' does not exist on this type
    return gUnionObj.a;
  }
  return 0;
}

// ============================================================
// 7. Combinators: !, &&, ||
// ============================================================

function testNegation(): string {
  if (!(gStr === null)) {
    // @skjs-expect-error Type of returned value is not assignable to the function's return type
    return gStr;
  }
  return "";
}

function testAndChain(a: boolean): string {
  if (a && gStr !== null) {
    // @skjs-expect-error Type of returned value is not assignable to the function's return type
    return gStr;
  }
  return "";
}

function testOrChain(a: boolean): string {
  if (gStr === null || !a) return "";
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return gStr;
}
