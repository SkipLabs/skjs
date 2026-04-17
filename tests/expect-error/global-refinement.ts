// Tests for type refinement applied to global (module-level) variables.
// Currently, SKJS narrowing calls scope.get(local) which only looks up
// locals — globals trigger an "Unbound name" error. This file documents
// the current behavior; a fix would remove these errors.

declare const gStr: string | null;
declare const gNum: number | undefined;
declare const gUnion: string | number;
declare const gBool: boolean;
declare const gArr: number[];
declare const gObj: { a?: number; kind?: "x" | "y" };
declare const gUnionObj: { a: number } | { b: string };
declare class MyCls {}
declare const gCls: MyCls | null;

// ============================================================
// 1. typeof narrowing
// ============================================================

function testTypeofString(): string {
  // @skjs-expect-error Unbound name
  if (typeof gStr === "string") return gStr;
  return "";
}

function testTypeofNumber(): number {
  // @skjs-expect-error Unbound name
  if (typeof gUnion === "number") return gUnion;
  return 0;
}

function testTypeofBoolean(): boolean {
  // @skjs-expect-error Unbound name
  if (typeof gBool === "boolean") return gBool;
  return false;
}

// ============================================================
// 2. null/undefined equality
// ============================================================

function testEqNull(): string {
  // @skjs-expect-error Unbound name
  if (gStr === null) return "";
  return gStr;
}

function testNeqNull(): string {
  // @skjs-expect-error Unbound name
  if (gStr !== null) return gStr;
  return "";
}

function testEqUndefined(): number {
  // @skjs-expect-error Unbound name
  if (gNum === undefined) return 0;
  return gNum;
}

function testNeqUndefined(): number {
  // @skjs-expect-error Unbound name
  if (gNum !== undefined) return gNum;
  return 0;
}

// ============================================================
// 3. Field equality narrowing (obj.field === constant)
// ============================================================

function testFieldEqConstant(): "x" {
  // @skjs-expect-error Unbound name
  if (gObj.kind === "x") return gObj.kind;
  return "x";
}

function testFieldNeqUndefined(): number {
  // @skjs-expect-error Unbound name
  if (gObj.a !== undefined) return gObj.a;
  return 0;
}

// ============================================================
// 4. Array.isArray
// ============================================================

function testIsArray(): number {
  // @skjs-expect-error Unbound name
  if (Array.isArray(gArr)) return gArr.length;
  return 0;
}

// ============================================================
// 5. instanceof
// ============================================================

function testInstanceOf(): string {
  // @skjs-expect-error Unbound name: gCls
  if (gCls instanceof MyCls) return "yes";
  return "no";
}

// ============================================================
// 6. "key" in obj
// ============================================================

function testInOperator(): number {
  // @skjs-expect-error Unbound name
  if ("a" in gUnionObj) return gUnionObj.a;
  return 0;
}

// ============================================================
// 7. Combinators: !, &&, ||
// ============================================================

function testNegation(): string {
  // @skjs-expect-error Unbound name
  if (!(gStr === null)) return gStr;
  return "";
}

function testAndChain(a: boolean): string {
  // @skjs-expect-error Unbound name
  if (a && gStr !== null) return gStr;
  return "";
}

function testOrChain(a: boolean): string {
  // @skjs-expect-error Unbound name
  if (gStr === null || !a) return "";
  return gStr;
}
