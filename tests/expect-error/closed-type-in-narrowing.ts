// `in` operator on Closed types (#802): a never-valued index proves its keys
// absent, so a provably-absent key check is always false and the true branch
// is unreachable.

function testInAbsentKeyAlwaysFalse(x: Closed<{ a: number }>): void {
  // @skjs-expect-warning This condition is always false
  if ("b" in x) {
    // The branch is unreachable: x narrows to never.
    const n: never = x;
  }
}

// A required key on a closed single-branch type: always true (already works
// via the never-aware accessible-index check).
function testInPresentKeyAlwaysTrue(x: Closed<{ a: number }>): void {
  // @skjs-expect-warning This condition is always true
  if ("a" in x) {
    const v = x.a;
  }
}

// An optional key can be present or absent: no warning, and the true branch
// narrows the field to non-optional.
function testInOptionalKeyNarrows(x: Closed<{ a?: number }>): void {
  if ("a" in x) {
    const v: number = x.a;
  }
}
