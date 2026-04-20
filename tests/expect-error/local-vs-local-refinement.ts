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
