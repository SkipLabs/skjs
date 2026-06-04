// truthiness mode "safe": a condition must be boolean, or have exactly one
// falsy value and at least one truthy value. Type-checking always continues
// with JavaScript semantics, so the rejected conditions still narrow normally.
//
// Rejections of number / multi-falsy unions / always-truthy / generics are
// SKJS-specific (tsc accepts them); the void rejection is shared with tsc.

// --- Accepted (single falsy) + narrowing ----------------------------------

function acceptObjUndef(o: { a: number } | undefined): void {
  // @skjs-expect-error A condition must be of type 'boolean'
  if (o) {
    // @skjs-expect-error Type of value is not assignable to the variable's type annotation
    const present: { a: number } = o;
  } else {
    // @skjs-expect-error Type of value is not assignable to the variable's type annotation
    const absent: undefined = o;
  }
}

function acceptString(s: string): void {
  // @skjs-expect-error A condition must be of type 'boolean'
  while (s) {
    break;
  }
}

function acceptNotBigint(b: bigint): boolean {
  // @skjs-expect-error Operand of '!' must be of type 'boolean'
  return !b;
}

function acceptTernary(o: { a: number } | null): number {
  // @skjs-expect-error A ternary condition must be of type 'boolean'
  return o ? 1 : 2;
}

// A literal union with one falsy member narrows on both sides.
function acceptLiteralUnion(x: 0 | 1): void {
  // @skjs-expect-error A condition must be of type 'boolean'
  if (x) {
    // @skjs-expect-error Type of value is not assignable to the variable's type annotation
    const one: 1 = x;
  } else {
    // @skjs-expect-error Type of value is not assignable to the variable's type annotation
    const zero: 0 = x;
  }
}

// Optional field: the then-branch drops optionality and undefined.
function acceptField(x: { f?: { a: number } }): void {
  // @skjs-expect-error A condition must be of type 'boolean'
  if (x.f) {
    // @skjs-expect-error Cannot access a property on type never
    const present: { a: number } = x.f;
  }
}

// --- Rejected --------------------------------------------------------------

function rejectNumber(n: number): void {
  // @skjs-expect-error A condition must be of type 'boolean'
  if (n) {
  }
}

function rejectStringUndefined(s: string | undefined): void {
  // @skjs-expect-error A condition must be of type 'boolean'
  if (s) {
  }
}

function rejectAlwaysTruthy(o: { a: number }): void {
  // @skjs-expect-error A condition must be of type 'boolean'
  if (o) {
  }
}

function rejectGeneric<T>(t: T): void {
  // @skjs-expect-error A condition must be of type 'boolean'
  if (t) {
  }
}

function rejectVoid(rv: () => void): void {
  // @skjs-expect-error A condition must be of type 'boolean'
  if (rv()) {
  }
}
