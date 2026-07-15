// An array-destructuring assignment writes each target the same way the
// equivalent single assignment would: a variable target is checked against its
// declared type and narrowed, and a property or index target is checked against
// the type it can be set to. Element types come from the right-hand side the
// same way a destructuring declaration derives them.

// FIXME: tsc rejects this write (TS2322) but SKJS currently accepts it: the
// destructuring target is not checked against its declared type at all.
function annotatedTargetIsChecked(): void {
  let x: string = "a";
  [x] = [5];
}

// FIXME: tsc rejects this write (TS2322) but SKJS currently accepts it.
function propertyTargetIsChecked(o: { f: string }): void {
  [o.f] = [5];
}

// FIXME: tsc rejects this write (TS2322) but SKJS currently accepts it.
function indexTargetIsChecked(a: string[]): void {
  [a[0]] = [5];
}

// A nested pattern destructures the element type in turn.
// FIXME: tsc rejects this write (TS2322) but SKJS currently accepts it.
function nestedTargetIsChecked(): void {
  let x: string = "a";
  [[x]] = [[5]];
}

// A captured target goes through the same write path, so the lambda's write is
// checked against the declared type like any other captured write.
// FIXME: tsc rejects this write (TS2322) but SKJS currently accepts it.
function capturedTargetIsChecked(): void {
  let x: string = "a";
  const g = () => {
    [x] = [5];
  };
  void g;
}

// A write of the declared type is accepted.
function targetOfDeclaredTypeAccepted(): void {
  let x: number = 0;
  [x] = [5];
  const n: number = x;
  void n;
}

// The right-hand side is evaluated before any target is written, so a swap
// works.
function swapAccepted(): void {
  let p: number = 1;
  let q: number = 2;
  [p, q] = [q, p];
}

// A rest target takes the remaining elements.
function restTargetAccepted(): void {
  let x: number = 0;
  let r: number[] = [];
  [x, ...r] = [1, 2, 3];
  void r;
}

// Without an annotation the inferred type evolves on assignment, here as much
// as for a single `x = 5`. SKJS is deliberately more permissive than tsc, which
// pins `let x = "a"` to `string` and rejects the write; the narrowing keeps this
// sound because reads see the written type.
function inferredTargetEvolves(): void {
  let x = "a";
  [x] = [5];
  // FIXME: the destructuring write does not narrow `x`, so it is still a
  // string here; a single `x = 5` would have evolved it to a number.
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const n: number = x;
  void n;
}
