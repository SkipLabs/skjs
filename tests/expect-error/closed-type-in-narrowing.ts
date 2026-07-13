// `in` operator on Closed types (#802): a never-valued index proves its keys
// absent, so a provably-absent key check is always false and the true branch
// is unreachable.

function testInAbsentKeyAlwaysFalse(x: Closed<{ a: number }>): void {
  // TODO(#802): should warn "This condition is always false".
  if ("b" in x) {
    // TODO(#802): the branch is unreachable; x should narrow to never.
    // @skjs-expect-error Type of value is not assignable to the variable's type annotation
    const n: never = x;
  }
}

// A required key on a closed single-branch type: always true (already works
// via the never-aware accessible-index check).
function testInPresentKeyAlwaysTrue(x: Closed<{ a: number }>): void {
  // @skjs-expect-error This condition is always true
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
