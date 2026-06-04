// truthiness mode "typescript": matches tsc. Everything is accepted except a
// purely-`void` condition (TS1345) and always-truthy function/method references
// (TS2774). A `void | T` union is accepted — only a whole-`void` condition is
// rejected, since the void part is non-observable. The rejected cases below are
// also rejected by tsc (annotated as ts errors).

// --- Accepted (tsc accepts these truthiness tests) -------------------------

function acceptNumber(n: number): void {
  if (n) {
  }
}

function acceptStringUndefined(s: string | undefined): void {
  if (s) {
  }
}

function acceptAlwaysTruthy(o: { a: number }): void {
  if (o) {
  }
}

function acceptGeneric<T>(t: T): void {
  if (t) {
  }
}

// `unknown` (the top type) is testable for truthiness in tsc, so `typescript`
// mode accepts it too.
function acceptUnknown(x: unknown): void {
  if (x) {
  }
}

function acceptObjUndef(o: { a: number } | undefined): void {
  if (o) {
    const present: { a: number } = o;
  }
}

// `void | T` is testable in tsc; only the void part is non-observable, so the
// condition is judged by the rest (here: number / undefined / boolean).
function acceptVoidNumber(x: void | number): void {
  if (x) {
  }
}

function acceptVoidUndefined(x: void | undefined): void {
  if (x) {
  }
}

function acceptVoidBoolean(x: void | boolean): void {
  if (x) {
  }
}

// `void | T` (unconstrained type variable) is likewise testable: the concrete
// `void` survives expansion but the type is not a whole-`void` condition, so
// tsc and `typescript` mode accept it (issue #657).
function acceptVoidTypeVar<T>(x: void | T): void {
  if (x) {
  }
}

// A class reference is always truthy but is not a call signature, so tsc (and
// SKJS) accept it.
class C {}
function acceptClass(): void {
  if (C) {
  }
}

// --- Rejected (tsc rejects these too) --------------------------------------

function rejectVoid(rv: () => void): void {
  // @ts-expect-error An expression of type void cannot be tested for truthiness
  if (rv()) {
  }
}

function rejectFunctionRef(fn: () => void): void {
  // @ts-expect-error This condition will always be true since this value is always defined
  if (fn) {
  }
}

function rejectMethodRef(o: { m(): void }): void {
  // @ts-expect-error This condition will always be true since this value is always defined
  if (o.m) {
  }
}
