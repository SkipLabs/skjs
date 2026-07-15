// `x instanceof C` for a generic class introduces fresh skolem parameters for
// the runtime object's hidden type arguments. Inference cannot choose them;
// code may use them abstractly or observe their declared bounds, but writes
// require the exact hidden type. If x's type already implies the test,
// narrowing preserves that type.

class Box<T> {
  v: T;
  constructor(v: T) {
    this.v = v;
  }
}

class Cell<T> {
  v: T;
  constructor(v: T) {
    this.v = v;
  }
  put(v: T): void {
    this.v = v;
  }
  take(): T {
    return this.v;
  }
}

class Tagged<T extends string> {
  tag: T;
  constructor(tag: T) {
    this.tag = tag;
  }
}

class SubBox<T> extends Box<T> {}

class Crate<T> {
  v: T;
  constructor(v: T) {
    this.v = v;
  }
}

class Pair<A, B> {
  left: A;
  right: B;
  constructor(left: A, right: B) {
    this.left = left;
    this.right = right;
  }
}

class WithCb<T> {
  v: T;
  constructor(v: T) {
    this.v = v;
  }
  pick(f: (item: T) => boolean): undefined | T {
    if (f(this.v)) {
      return this.v;
    }
    return undefined;
  }
  put(v: T): void {
    this.v = v;
  }
}

// Read side: an expected type must not determine the skolem parameter.
function rejectConcreteRead(x: unknown): string {
  if (x instanceof Box) {
    const s: string = x.v;
    return s;
  }
  return "no";
}

// Write side: a write must not determine the skolem parameter.
function rejectConcreteWrite(a: Box<number>): number {
  const x: unknown = a;
  if (x instanceof Box) {
    x.v = "s";
  }
  return a.v;
}

// A second check must not expose the hidden type argument (nested form).
function nestedConcreteRead(x: unknown): string {
  if (x instanceof Box) {
    if (x instanceof Box) {
      return x.v;
    }
  }
  return "no";
}

// Method arguments are the write side too.
function rejectMethodWrite(x: unknown): void {
  if (x instanceof Cell) {
    x.put(3);
  }
}

// Checks of two objects introduce distinct skolems, so values cannot cross.
function crossExchange(x: unknown, y: unknown): void {
  if (x instanceof Box && y instanceof Box) {
    x.v = y.v;
  }
}

// One check introduces a distinct skolem for each class type parameter.
function pairArgumentsDistinct(x: unknown): void {
  if (x instanceof Pair) {
    x.left = x.right;
  }
}

// A declared bound does not license writes below it.
function boundedWrite(x: unknown): void {
  if (x instanceof Tagged) {
    x.tag = "a";
  }
}

// The narrowed value is not admissible at a concrete instantiation.
declare function takesBoxString(b: Box<string>): void;
function concreteAdmission(x: unknown): void {
  if (x instanceof Box) {
    takesBoxString(x);
  }
}

// Generic subclasses preserve hidden type arguments the same way.
function subclassWrite(x: unknown): void {
  if (x instanceof SubBox) {
    x.v = "s";
  }
}

// An unbounded hidden type argument can be read as unknown.
function observe(x: unknown): void {
  if (x instanceof Box) {
    const u: unknown = x.v;
  }
}

// A declared bound is visible through the read.
function boundedRead(x: unknown): string {
  if (x instanceof Tagged) {
    return x.tag;
  }
  return "no";
}

// Round-trips through the same occurrence are accepted (equality fast path).
function roundTrip(x: unknown): void {
  if (x instanceof Cell) {
    x.put(x.take());
  }
}

// Idempotence: redundant narrowing of an already-typed scrutinee is the
// identity — reads keep the precise type and parameter-typed methods keep
// their signatures.
function typedIdentity(x: Cell<number>): number {
  if (x instanceof Cell) {
    x.put(3);
    return x.v;
  }
  return 0;
}

// Union scrutinee: the matching arm keeps its precise arguments.
function unionScrutinee(x: Box<number> | string): number {
  if (x instanceof Box) {
    return x.v;
  }
  return 0;
}

// Checks against two different generic classes introduce independent skolems;
// a shared field must not make either hidden type argument escape.
function crossClassRead(x: unknown): string {
  if (x instanceof Box && x instanceof Crate) {
    return x.v;
  }
  return "";
}

// Generic call-site inference accepts a skolem instantiation (T := s)
// without letting the result escape its unknown bound.
declare function ident<A>(a: A): A;
function genericFlow(x: unknown): string {
  if (x instanceof Box) {
    const u: unknown = ident(x.v);
    return JSON.stringify(x.v);
  }
  return "";
}

// A value can round-trip after the skolem passes through `undefined | T`.
function unionRoundTrip(x: unknown): void {
  if (x instanceof WithCb) {
    const selected = x.pick((_item) => true);
    if (selected !== undefined) {
      x.put(selected);
    }
  }
}

// A hidden type argument does not escape its bound through generic identity.
function hiddenTypeNoEscape(x: unknown): string {
  if (x instanceof Box) {
    return ident(x.v);
  }
  return "";
}

// One inferred readonly element type can cover two skolems by growing to their
// union.
declare function sharedRO<T>(a: ReadonlyArray<T>, b: ReadonlyArray<T>): number;
function sharedReadOnly(u: unknown, w: unknown): number {
  if (u instanceof Array && w instanceof Array) {
    return sharedRO(u, w);
  }
  return 0;
}

// `instanceof Array` introduces a hidden element type, so writes are rejected.
function arrayWrite(a: Array<number>): number {
  const x: unknown = a;
  if (x instanceof Array) {
    x[0] = "s";
  }
  return a.length;
}

// The same applies to element-consuming methods.
function arrayPush(a: Array<number>): number {
  const x: unknown = a;
  if (x instanceof Array) {
    x.push("s");
  }
  return a.length;
}

// Element-independent reads remain valid.
function arrayRead(x: unknown): void {
  if (x instanceof Array) {
    const e: unknown = x[0];
    const len: number = x.length;
  }
}

// A typed array retains its precise element type after a redundant check.
function typedArrayIdentity(a: Array<number>): void {
  if (a instanceof Array) {
    a.push(3);
    a[0] = 5;
  }
}

// Independently narrowed arrays flow into separate type parameters.
declare function eachLen<A, B>(a: Array<A>, b: Array<B>): number;
function separateArrayParams(u: unknown, w: unknown): number {
  if (u instanceof Array && w instanceof Array) {
    return eachLen(u, w);
  }
  return 0;
}

// One type parameter over two independently narrowed arrays claims their
// elements are exchangeable — rightly rejected on the write surface.
declare function sharedLen<T>(a: Array<T>, b: Array<T>): number;
function rejectSharedArrayElement(u: unknown, w: unknown): number {
  if (u instanceof Array && w instanceof Array) {
    return sharedLen(u, w);
  }
  return 0;
}

/* -------------------------------------------------------------------------
 * Known holes: accepted today, unsound at runtime.
 *
 * A skolem is minted once per type-check of a scope, but it stands for the
 * hidden argument of whichever object each *runtime execution* of that scope
 * narrows. Any channel that lets a skolem-typed value outlive one execution
 * pools distinct hidden arguments under one identity and permits
 * cross-object writes. The functions below type-check with no diagnostics;
 * each contains a write that corrupts an object at runtime (marked
 * `UNSOUND`). They are pinned here as accepted so that when a fix lands,
 * this suite fails loudly and the cases get flipped to expect-error
 * annotations. See the commit message of the change introducing skolem
 * narrowing for the analysis and the prototyped (unlanded) fixes.
 * ----------------------------------------------------------------------- */

declare function makeList<T>(): T[];

// Hole 1 — inferred closure results. The arrow body is checked once, so
// every call's result is typed with the same skolem. At runtime p is
// Box<number> and q is Box<string>; the write puts a string in a
// Box<number>, and `return a.v` then yields a string from a
// number-returning function.
function holeSharedClosureResult(a: Box<number>, b: Box<string>): number {
  const reveal = (x: unknown) => {
    if (x instanceof Box) return x;
    throw 0;
  };
  const p = reveal(a);
  const q = reveal(b);
  p.v = q.v; // UNSOUND: accepted, writes string into Box<number>
  return a.v;
}

// Hole 1b — the higher-order face of the same sharing: generic inference
// retains the skolem in R, so one call's Pair holds two runtime-distinct
// objects under one hidden type, and results of separate calls unify too.
declare function applyTwo<R>(
  f: (x: unknown) => R,
  a: unknown,
  b: unknown,
): Pair<R, R>;
function holeHigherOrderResult(a: Box<number>, b: Box<string>): number {
  const reveal = (x: unknown) => {
    if (x instanceof Box) return x;
    throw 0;
  };
  const pair = applyTwo(reveal, a, b);
  pair.left.v = pair.right.v; // UNSOUND: accepted, writes string into Box<number>
  return a.v;
}

// Hole 2 — captured mutable state. The container's inferred element type
// outlives one execution of the arrow, so values stored by separate calls
// become exchangeable.
function holeCapturedContainer(a: Box<number>, b: Box<string>): number {
  const ys = makeList();
  const store = (x: unknown) => {
    if (x instanceof Box) {
      ys.push(x);
    }
  };
  store(a);
  store(b);
  const p = ys[0];
  const q = ys[1];
  if (p && q) {
    p.v = q.v; // UNSOUND: accepted, writes string into Box<number>
  }
  return a.v;
}

// Hole 3 — loop bodies, no closure needed. The body is checked once, so all
// iterations share one skolem and their values pool in the outer container.
function holeLoopPooling(items: unknown[]): void {
  const ys = makeList();
  for (const x of items) {
    if (x instanceof Box) {
      ys.push(x);
    }
  }
  const p = ys[0];
  const q = ys[1];
  if (p && q) {
    p.v = q.v; // UNSOUND: accepted, exchanges elements of distinct hidden types
  }
}
