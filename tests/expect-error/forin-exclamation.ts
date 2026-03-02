///////////////////////////////////////////////////////////////////////////////
// Tests for safe v[k]! inside for-in loops
///////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////
// Safe cases: v[k]! at start of for-in loop body (no side effects before it)
///////////////////////////////////////////////////////////////////////////////

function testForInBasic(v: { [key: string]: number }): void {
  for (const k in v) {
    const val: number = v[k]!;
  }
}

function testForInDotAccess(obj: { field: { [key: string]: number } }): void {
  for (const k in obj.field) {
    const val: number = obj.field[k]!;
  }
}

function testForInDeepDotAccess(a: {
  b: { c: { [key: string]: number } };
}): void {
  for (const k in a.b.c) {
    const val: number = a.b.c[k]!;
  }
}

function testForInThenCall(v: { [key: string]: number }): void {
  for (const k in v) {
    const val: number = v[k]!;
    someFunc();
  }
}

///////////////////////////////////////////////////////////////////////////////
// Unsafe cases: v[k]! after side effects in for-in loop
///////////////////////////////////////////////////////////////////////////////

function testForInAfterCall(v: { [key: string]: number }): void {
  for (const k in v) {
    someFunc();
    // @skjs-expect-error Do not use the postfix ! operator
    const val: number = v[k]!;
  }
}

function testForInAfterNew(v: { [key: string]: number }): void {
  for (const k in v) {
    const _x = new SomeClass();
    // @skjs-expect-error Do not use the postfix ! operator
    const val: number = v[k]!;
  }
}

function testForInDotAccessAfterCall(obj: {
  field: { [key: string]: number };
}): void {
  for (const k in obj.field) {
    someFunc();
    // @skjs-expect-error Do not use the postfix ! operator
    const val: number = obj.field[k]!;
  }
}

///////////////////////////////////////////////////////////////////////////////
// Still-banned cases: not a for-in v[k]! pattern
///////////////////////////////////////////////////////////////////////////////

function testForInWrongObject(
  v: { [key: string]: number },
  w: { [key: string]: number },
): void {
  for (const k in v) {
    // @skjs-expect-error Do not use the postfix ! operator
    const val: number = w[k]!;
  }
}

function testForInObjectMismatch(
  v: { [key: string]: number },
  v2: { [key: string]: number },
): void {
  for (const x in v2) {
    // @skjs-expect-error Do not use the postfix ! operator
    const val: number = v[x]!;
  }
}

function testRegularExclamation(x: number | null): number {
  // @skjs-expect-error Do not use the postfix ! operator
  return x!;
}

function testForOfExclamation(v: { [key: string]: number }): void {
  const arr: (number | null)[] = [1, null, 3];
  for (const x of arr) {
    // @skjs-expect-error Do not use the postfix ! operator
    const val: number = x!;
  }
}

///////////////////////////////////////////////////////////////////////////////
// Helpers (type-only, never called)
///////////////////////////////////////////////////////////////////////////////

declare function someFunc(): void;
declare class SomeClass {}
