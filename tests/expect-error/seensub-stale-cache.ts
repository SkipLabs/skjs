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
  // @skjs-expect-error Type argument does not satisfy the constraint
  y: Constrained<U>,
  // @skjs-expect-error Type argument does not satisfy the constraint
): Constrained<U> {
  return x;
}

// ============================================================
// With the fix, SKJS properly rejects all of these.
// ============================================================

function testUnsound(): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  const box = getFirst({ value: "hello" }, { value: 42 });
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const n: number = box.value;
}

function testReversedOrder(): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  const box = getFirst({ value: 42 }, { value: "hello" });
  const n: number = box.value;
}

function testThreeArgs(): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  const box = getFirst3({ value: true }, { value: 42 }, { value: 100 });
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const n: number = box.value;
}

function getFirst3<U>(
  x: Constrained<U>,
  // @skjs-expect-error Type argument does not satisfy the constraint
  y: Constrained<U>,
  // @skjs-expect-error Type argument does not satisfy the constraint
  z: Constrained<U>,
  // @skjs-expect-error Type argument does not satisfy the constraint
): Constrained<U> {
  return x;
}

// ============================================================
// Control: both arguments valid — should pass
// ============================================================

function testBothValidWithoutAnnot(): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  const box = getFirst({ value: 42 }, { value: 100 });
  const n: number = box.value;
}

function testBothValidWithAnnot(): void {
  const box = getFirst<42 | 100>({ value: 42 }, { value: 100 });
  const n: number = box.value;
}
