// truthiness mode "typescript": matches tsc. Everything is accepted except
// void (TS1345) and always-truthy function/method references (TS2774). The
// rejected cases below are also rejected by tsc (annotated as ts errors).

// --- Accepted (tsc accepts these truthiness tests) -------------------------

function acceptNumber(n: number): void {
  // @skjs-expect-error A condition must be of type 'boolean'
  if (n) {
  }
}

function acceptStringUndefined(s: string | undefined): void {
  // @skjs-expect-error A condition must be of type 'boolean'
  if (s) {
  }
}

function acceptAlwaysTruthy(o: { a: number }): void {
  // @skjs-expect-error A condition must be of type 'boolean'
  if (o) {
  }
}

function acceptGeneric<T>(t: T): void {
  // @skjs-expect-error A condition must be of type 'boolean'
  if (t) {
  }
}

function acceptObjUndef(o: { a: number } | undefined): void {
  // @skjs-expect-error A condition must be of type 'boolean'
  if (o) {
    // @skjs-expect-error Type of value is not assignable to the variable's type annotation
    const present: { a: number } = o;
  }
}

// A class reference is always truthy but is not a call signature, so tsc (and
// SKJS) accept it.
class C {}
function acceptClass(): void {
  // @skjs-expect-error A condition must be of type 'boolean'
  if (C) {
  }
}

// --- Rejected (tsc rejects these too) --------------------------------------

function rejectVoid(rv: () => void): void {
  // @skjs-expect-error A condition must be of type 'boolean'
  if (rv()) {
  }
}

function rejectFunctionRef(fn: () => void): void {
  // @skjs-expect-error A condition must be of type 'boolean'
  if (fn) {
  }
}

function rejectMethodRef(o: { m(): void }): void {
  // @skjs-expect-error A condition must be of type 'boolean'
  if (o.m) {
  }
}
