// Tests for #584: narrowing two locals compared to each other.
// `if (x === y)` should narrow both x and y to inter(x.type, y.type).
// `if (x !== y)` where one side is a singleton constant should diff.

// ============================================================
// 1. One side is a singleton local type
// ============================================================

function testSingletonRhsNarrowsLhs(x: string | null, y: null): void {
  if (x === y) {
    const z: null = x;
  }
}

function testSingletonLhsNarrowsRhs(x: null, y: string | null): void {
  if (x === y) {
    const z: null = y;
  }
}

// ============================================================
// 2. Both sides are unions with overlap: narrow to intersection
// ============================================================

function testBothOverlapNarrowsLhs(x: "a" | "b", y: "b" | "c"): void {
  if (x === y) {
    const a: "b" = x;
  }
}

function testBothOverlapNarrowsRhs(x: "a" | "b", y: "b" | "c"): void {
  if (x === y) {
    const b: "b" = y;
  }
}

// ============================================================
// 3. !== with one side a singleton: diff from the other
// ============================================================

function testNeqSingleton(x: string | null, y: null): void {
  if (x !== y) {
    const s: string = x;
  }
}

// ============================================================
// 4. !== with no singletons: no narrowing (intended)
// ============================================================

function testNeqNoSingleton(x: "a" | "b", y: "b" | "c"): void {
  if (x !== y) {
    // Both types stay unchanged
    const a: "a" | "b" = x;
    const b: "b" | "c" = y;
  }
}

// ============================================================
// 5. Combinators: narrowing propagates through && / ||
// ============================================================

function testAndChain(x: string | null, y: null, cond: boolean): void {
  if (cond && x === y) {
    const z: null = x;
  }
}

// ============================================================
// 6. Order independence: y === x narrows the same
// ============================================================

function testReversedOrder(x: null, y: string | null): void {
  if (y === x) {
    const z: null = y;
  }
}

// ============================================================
// 7. Var vs arbitrary expression (literal, call, field)
// ============================================================

function testVarVsLiteral(x: 0 | 1 | 2): void {
  if (x === 1) {
    const n: 1 = x;
  }
}

declare function getOneOrTwo(): 1 | 2;

function testVarVsCall(x: 0 | 1 | 2): void {
  if (x === getOneOrTwo()) {
    const n: 1 | 2 = x;
  }
}

declare const globalObj: { v: 1 | 2 };

function testVarVsGlobalField(x: 0 | 1 | 2): void {
  if (x === globalObj.v) {
    const n: 1 | 2 = x;
  }
}

// ============================================================
// 8. Var vs local field: both the var and the field narrow
// ============================================================

function testVarVsLocalFieldNarrowsVar(x: 0 | 1 | 2, o: { v: 1 | 2 }): void {
  if (x === o.v) {
    const n: 1 | 2 = x;
  }
}

function testVarVsLocalFieldNarrowsField(x: 1, o: { v: 0 | 1 | 2 }): void {
  if (x === o.v) {
    const v: 1 = o.v;
  }
}

// ============================================================
// 9. Field vs field: both sides narrow to the intersection
// ============================================================

function testFieldVsFieldNarrowsBoth(
  o1: { a: 0 | 1 | 2 },
  o2: { b: 1 | 2 | 3 },
): void {
  if (o1.a === o2.b) {
    const a: 1 | 2 = o1.a;
    const b: 1 | 2 = o2.b;
  }
}
