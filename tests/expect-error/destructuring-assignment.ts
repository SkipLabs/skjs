// An array-destructuring assignment writes each target the same way the
// equivalent single assignment would: a variable target is checked against its
// declared type and narrowed, and a property or index target is checked against
// the type it can be set to. Element types come from the right-hand side the
// same way a destructuring declaration derives them.

function annotatedTargetIsChecked(): void {
  let x: string = "a";
  // @ts-expect-error Type is not assignable to the variable's type
  [x] = [5];
}

function propertyTargetIsChecked(o: { f: string }): void {
  // @ts-expect-error Type is not assignable to the assignment target's type
  [o.f] = [5];
}

function indexTargetIsChecked(a: string[]): void {
  // @ts-expect-error Type is not assignable to the assignment target's type
  [a[0]] = [5];
}

// A nested pattern destructures the element type in turn.
function nestedTargetIsChecked(): void {
  let x: string = "a";
  // @ts-expect-error Type is not assignable to the variable's type
  [[x]] = [[5]];
}

// A captured target goes through the same write path, so the lambda's write is
// checked against the declared type like any other captured write.
function capturedTargetIsChecked(): void {
  let x: string = "a";
  const g = () => {
    // @ts-expect-error Type is not assignable to the variable's type
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

// A rest target takes the remaining elements: the rest of a tuple can be read
// as a tuple.
function restTargetOfTupleAccepted(): void {
  let x: number = 0;
  let r: [number, number] = [0, 0];
  [x, ...r] = [1, 2, 3];
  void r;
}

// ...and equally as an array: destructuring a rest allocates a fresh array, so
// nothing aliases it at a fixed arity and it may be read as a growable array.
// (An existing tuple stays un-assignable to an array — see
// restDoesNotLetATupleBecomeAnArray.)
function restTargetOfTupleAsArrayAccepted(): void {
  let x: number = 0;
  let r: number[] = [];
  [x, ...r] = [1, 2, 3];
  void r;
}

// The rest's elements are still checked, whichever shape the target asks for.
function restTargetElementsAreChecked(): void {
  let x: number = 0;
  let r: string[] = [];
  // @ts-expect-error Type is not assignable to the variable's type
  [x, ...r] = [1, 2, 3];
  void r;
}

// A rest that takes nothing is an empty array.
function emptyRestTargetAccepted(): void {
  let x: number = 0;
  let r: number[] = [];
  [x, ...r] = [1];
  void r;
}

// The aliasing case this must not regress: an existing tuple is not an array,
// because writing through the array view would break the tuple's arity.
function restDoesNotLetATupleBecomeAnArray(): void {
  const tup: [number, number] = [1, 2];
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const a: number[] = tup;
  void a;
}

// Destructuring anything else iterable takes the iterator's element type, and
// the rest is an array of it. An element may be missing, so it is widened with
// `undefined` — the same rule a declaration uses.
function restTargetOfArrayAccepted(src: number[]): void {
  let x: number | undefined = 0;
  let r: number[] = [];
  [x, ...r] = src;
  void r;
}

// Without an annotation the inferred type evolves on assignment, here as much
// as for a single `x = 5`. SKJS is deliberately more permissive than tsc, which
// pins `let x = "a"` to `string` and rejects the write; the narrowing keeps this
// sound because reads see the written type.
function inferredTargetEvolves(): void {
  let x = "a";
  [x] = [5];
  const n: number = x;
  void n;
}

function keyBeforeDefault(): number {
  let value: number | null = null;
  const box: { slot: number } = { slot: 0 };
  // @skjs-expect-error Type is not assignable to the assignment target's type
  [box[(value = 1) === 1 ? "slot" : "slot"] = value] = [undefined];
  return box.slot;
}
function keyClearsDefault(): void {
  let value: number | null = 1;
  const box: { slot: number } = { slot: 0 };
  if (value === null) return;
  [box[(value = null) === null ? "slot" : "slot"] = value] = [undefined];
}
