// truthiness mode "safe": a condition must be boolean, or have exactly one
// falsy value and at least one truthy value. Type-checking always continues
// with JavaScript semantics, so the rejected conditions still narrow normally.
//
// Rejections of number / multi-falsy unions / always-truthy / generics are
// SKJS-specific (tsc accepts them). `safe` also rejects any condition whose
// type contains `void` (stricter than tsc, which rejects only a purely-`void`
// condition); pure `void` is shared with tsc.

// --- Accepted (single falsy) + narrowing ----------------------------------

function acceptObjUndef(o: { a: number } | undefined): void {
  if (o) {
    const present: { a: number } = o;
  } else {
    const absent: undefined = o;
  }
}

function acceptString(s: string): void {
  while (s) {
    break;
  }
}

function acceptNotBigint(b: bigint): boolean {
  return !b;
}

function acceptTernary(o: { a: number } | null): number {
  return o ? 1 : 2;
}

// A literal union with one falsy member narrows on both sides.
function acceptLiteralUnion(x: 0 | 1): void {
  if (x) {
    const one: 1 = x;
  } else {
    const zero: 0 = x;
  }
}

// Optional field: the then-branch drops optionality and undefined.
function acceptField(x: { f?: { a: number } }): void {
  if (x.f) {
    const present: { a: number } = x.f;
  }
}

// --- Rejected --------------------------------------------------------------

function rejectNumber(n: number): void {
  // @skjs-expect-error A condition is expected to be of type boolean or a type with a single falsy value
  if (n) {
  }
}

function rejectStringUndefined(s: string | undefined): void {
  // @skjs-expect-error A condition is expected to be of type boolean or a type with a single falsy value
  if (s) {
  }
}

function rejectAlwaysTruthy(o: { a: number }): void {
  // @skjs-expect-error A condition is expected to be of type boolean or a type with a single falsy value
  if (o) {
  }
}

function rejectGeneric<T>(t: T): void {
  // @skjs-expect-error A condition is expected to be of type boolean or a type with a single falsy value
  if (t) {
  }
}

// `unknown` (the top type) could be any value, so it is not a single-falsy
// condition; tsc accepts it, so this is SKJS-only.
function rejectUnknown(x: unknown): void {
  // @skjs-expect-error A condition is expected to be of type boolean or a type with a single falsy value
  if (x) {
  }
}

function rejectVoid(rv: () => void): void {
  // @ts-expect-error An expression of type void cannot be tested for truthiness
  if (rv()) {
  }
}

// `safe` rejects any void member, even in a union tsc accepts (so this is an
// SKJS-only error, unlike pure `void` above which tsc also rejects).
function rejectVoidUnion(x: void | number): void {
  // @skjs-expect-error An expression of type void cannot be tested for truthiness
  if (x) {
  }
}

// The `void` member is still flagged when unioned with an unconstrained type
// variable (issue #657); tsc accepts `void | T`, so this is SKJS-only.
function rejectVoidTypeVar<T>(x: void | T): void {
  // @skjs-expect-error An expression of type void cannot be tested for truthiness
  if (x) {
  }
}

// A radix-spelled zero (here octal `0o0`) is a falsy value just like decimal
// `0`, so `0o0 | 1` is single-falsy: accepted, and narrowed to `1` in the then-
// branch and `0o0` in the else-branch (issue #655).
function acceptOctalZero(x: 0o0 | 1): void {
  if (x) {
    const t: 1 = x;
  } else {
    const e: 0o0 = x;
  }
}
