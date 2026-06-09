// Regression tests for issue #89: narrowing through && and ||.
// Historically SKJS mis-narrowed `x === null || true` (filtering x as if
// `x === null` were the only way to enter) and failed to narrow through
// `x === null && true`. Both work correctly now.

type N = { a: number };

// `x === null || true`: the whole condition is tautologically true,
// so no narrowing should apply — x remains N | null.
function testOrTrueNoRefinement(x: N | null): void {
  if (x === null || true) {
    // x is still N | null
    // @skjs-expect-error Property access is not allowed on this type
    const a: number = x.a;
  }
}

// `x === null && true`: both operands must be true, so x narrows to null.
function testAndTrueRefines(x: N | null): void {
  if (x === null && true) {
    const y: null = x;
  }
}

// `x !== null && x.a > 0`: left narrows x to N, enabling x.a in the right.
function testAndChainRefines(x: N | null): void {
  if (x !== null && x.a > 0) {
    const y: N = x;
  }
}

// `x === null || other`: in the then-branch, x could still be null
// (if e1 was true), so no narrowing to N should apply.
function testOrLeftEqNullNoPosRefinement(x: N | null, other: boolean): void {
  if (x === null || other) {
    // @skjs-expect-error Property access is not allowed on this type
    const a: number = x.a;
  }
}
