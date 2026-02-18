// Regression test for stale seenSub cache in Subst save/restore.
//
// Before the fix, Subst::save()/restore() only saved `version` and `values`,
// leaving `seenSub`, `seenInter`, `seenUnion` with stale entries. Combined
// with constraint-based narrowing, this produced unsound type inference:
// SKJS would assign type `number` to a value that is `"hello"` at runtime.

// ============================================================
// Setup
// ============================================================

interface Constrained<T extends number> {
  value: T;
}

function getFirst<U>(
  x: Constrained<U>,
  // @skjs-expect-error Constraint not satisfied
  y: Constrained<U>,
  // @skjs-expect-error Constraint not satisfied
): Constrained<U> {
  return x;
}

// ============================================================
// With the fix, SKJS properly rejects all of these.
// ============================================================

function testUnsound(): void {
  const box = getFirst({ value: "hello" }, { value: 42 });
  // @skjs-expect-error Invalid annotation
  const n: number = box.value;
}

function testReversedOrder(): void {
  const box = getFirst({ value: 42 }, { value: "hello" });
  // @skjs-expect-error Invalid annotation
  const n: number = box.value;
}

function testThreeArgs(): void {
  const box = getFirst3({ value: true }, { value: 42 }, { value: 100 });
  // @skjs-expect-error Invalid annotation
  const n: number = box.value;
}

function getFirst3<U>(
  x: Constrained<U>,
  // @skjs-expect-error Constraint not satisfied
  y: Constrained<U>,
  // @skjs-expect-error Constraint not satisfied
  z: Constrained<U>,
  // @skjs-expect-error Constraint not satisfied
): Constrained<U> {
  return x;
}

// ============================================================
// Control: both arguments valid — should pass
// ============================================================

function testBothValid(): void {
  const box = getFirst({ value: 42 }, { value: 100 });
  const n: number = box.value;
}
