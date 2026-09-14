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
    // @skjs-expect-error Type of value is not assignable to the variable's type annotation
    // @skjs-expect-error-line2 Type 'Box#T'
    // @skjs-expect-error-line3 is not assignable to type 'string'
    const s: string = x.v;
    return s;
  }
  return "no";
}

// Write side: a write must not determine the skolem parameter.
function rejectConcreteWrite(a: Box<number>): number {
  const x: unknown = a;
  if (x instanceof Box) {
    // @skjs-expect-error Type is not assignable to the assignment target's type
    // @skjs-expect-error-line2 Type 'string'
    // @skjs-expect-error-line3 is not assignable to type 'Box#T'
    x.v = "s";
  }
  return a.v;
}

// A second check must not expose the hidden type argument (nested form).
function nestedConcreteRead(x: unknown): string {
  if (x instanceof Box) {
    if (x instanceof Box) {
      // @skjs-expect-error Type of returned value is not assignable to the function's return type
      // @skjs-expect-error-line2 Type 'Box#T'
      // @skjs-expect-error-line3 is not assignable to type 'string'
      return x.v;
    }
  }
  return "no";
}

// Method arguments are the write side too.
function rejectMethodWrite(x: unknown): void {
  if (x instanceof Cell) {
    // @skjs-expect-error Argument is not assignable to the parameter's type
    // @skjs-expect-error-line2 Type 'number'
    // @skjs-expect-error-line3 is not assignable to type 'Cell#T'
    x.put(3);
  }
}

// Checks of two objects introduce distinct skolems, so values cannot cross.
function crossExchange(x: unknown, y: unknown): void {
  if (x instanceof Box && y instanceof Box) {
    // @skjs-expect-error Type is not assignable to the assignment target's type
    // @skjs-expect-error-line2 Type 'Box#T#2'
    // @skjs-expect-error-line3 is not assignable to type 'Box#T#1'
    x.v = y.v;
  }
}

// One check introduces a distinct skolem for each class type parameter.
function pairArgumentsDistinct(x: unknown): void {
  if (x instanceof Pair) {
    // @skjs-expect-error Type is not assignable to the assignment target's type
    // @skjs-expect-error-line2 Type 'Pair#B'
    // @skjs-expect-error-line3 is not assignable to type 'Pair#A'
    x.left = x.right;
  }
}

// A declared bound does not license writes below it.
function boundedWrite(x: unknown): void {
  if (x instanceof Tagged) {
    // @skjs-expect-error Type is not assignable to the assignment target's type
    // @skjs-expect-error-line2 Type 'string'
    // @skjs-expect-error-line3 is not assignable to type 'Tagged#T extends string'
    x.tag = "a";
  }
}

// The narrowed value is not admissible at a concrete instantiation.
declare function takesBoxString(b: Box<string>): void;
function concreteAdmission(x: unknown): void {
  if (x instanceof Box) {
    // @skjs-expect-error Argument is not assignable to the parameter's type
    // @skjs-expect-error-line2 Type 'Box#T'
    // @skjs-expect-error-line3 is not assignable to type 'string'
    takesBoxString(x);
  }
}

// Generic subclasses preserve hidden type arguments the same way.
function subclassWrite(x: unknown): void {
  if (x instanceof SubBox) {
    // @skjs-expect-error Type is not assignable to the assignment target's type
    // @skjs-expect-error-line2 Type 'string'
    // @skjs-expect-error-line3 is not assignable to type 'SubBox#T'
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

// An object arm that does not already satisfy the test survives as
// `arm & Box<T>` -- width subtyping lets a `{ a: number }` value carry a `v`
// and be a Box -- so reading `v` across the union is `string | T`, not
// `string`. The skolem is what keeps the arms apart: with one shared inference
// variable the matching arm sealed it to `string`, and the other arm then also
// claimed its hidden argument was `string`, which is #772 in union form (a
// `Box<number>` inhabiting `{ a: number }` returned its number as a string).
// tsc drops the arm entirely and answers `string`; SKJS cannot, and must not.
function unionObjectArm(o: { a: number } | Box<string>): string {
  if (o instanceof Box) {
    // @skjs-expect-error Type of returned value is not assignable to the function's return type
    // @skjs-expect-error-line2 Type 'string | Box#T'
    // @skjs-expect-error-line3 is not assignable to type 'string'
    return o.v;
  }
  return "";
}

// Checks against two different generic classes introduce independent skolems;
// a shared field must not make either hidden type argument escape.
function crossClassRead(x: unknown): string {
  if (x instanceof Box && x instanceof Crate) {
    // @skjs-expect-error Type of returned value is not assignable to the function's return type
    // @skjs-expect-error-line2 Type 'Box#T'
    // @skjs-expect-error-line3 is not assignable to type 'string'
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

// A hidden type argument does not become its bound by passing through generic
// identity: `A := T` and `T` is not `string`, so the return is rejected.
function hiddenTypeNoEscape(x: unknown): string {
  if (x instanceof Box) {
    // @skjs-expect-error Type of returned value is not assignable to the function's return type
    // @skjs-expect-error-line2 Type 'Box#T'
    // @skjs-expect-error-line3 is not assignable to type 'string'
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
    // @skjs-expect-error Type is not assignable to the assignment target's type
    // @skjs-expect-error-line2 Type 'string'
    // @skjs-expect-error-line3 is not assignable to type 'Array#T'
    x[0] = "s";
  }
  return a.length;
}

// The same applies to element-consuming methods.
function arrayPush(a: Array<number>): number {
  const x: unknown = a;
  if (x instanceof Array) {
    // @skjs-expect-error Argument is not assignable to the parameter's type
    // @skjs-expect-error-line2 Type 'string'
    // @skjs-expect-error-line3 is not assignable to type 'Array#T'
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
    // @skjs-expect-error Argument is not assignable to the parameter's type
    // @skjs-expect-error-line2 Type 'Array#T#2'
    // @skjs-expect-error-line3 is not assignable to type 'Array#T#1'
    // @skjs-expect-error-line4 Consider adding explicit type arguments
    // @skjs-expect-error-line5 Function parameter types are checked contravariantly: target parameter type 'Array#T#2' must be assignable to source parameter type 'Array#T#1'
    return sharedLen(u, w);
  }
  return 0;
}

// Narrowing a value that is already a Box must be the identity, and must not
// depend on how its type was spelled. These two functions take the same type
// written two ways: `Box<string> | Box<number>` keeps its arms as unexpanded
// instances in separate clauses, while `{ v: string } | { v: number }` is ONE
// TObject holding two TFields branches (STypes is keyed by tag, so every
// object arm merges into one).
//
// The write is rejected before the narrowing in both -- the setter is
// `string & number`, so no value can be written -- and must stay rejected
// after it. Accepting `o.v = o.v` would be harmless in itself (it is a
// self-assignment, and the value came from this same object); what must not
// happen is the two spellings disagreeing. They did: the preservation check
// ran once for the whole TObject, no single `Box<T>` covers both branches, so
// the inline spelling failed the check, had both branches intersected with the
// skolem, and came back with setters widened to `string | T` / `number | T` --
// admitting the write that the instance spelling refused.
function multiBranchInstsWriteBefore(o: Box<string> | Box<number>): void {
  // @skjs-expect-error Type is not assignable to the assignment target's type
  // @skjs-expect-error-line2 Type 'number | string'
  // @skjs-expect-error-line3 is not assignable to type 'number & string'
  o.v = o.v;
}

function multiBranchInstsWriteAfter(o: Box<string> | Box<number>): void {
  if (o instanceof Box) {
    // @skjs-expect-error Type is not assignable to the assignment target's type
    // @skjs-expect-error-line2 Type 'number | string'
    // @skjs-expect-error-line3 is not assignable to type 'number & string'
    o.v = o.v;
  }
}

function multiBranchInlineWriteBefore(o: { v: string } | { v: number }): void {
  // @skjs-expect-error Type is not assignable to the assignment target's type
  // @skjs-expect-error-line2 Type 'number | string'
  // @skjs-expect-error-line3 is not assignable to type 'number & string'
  o.v = o.v;
}

function multiBranchInlineWriteAfter(o: { v: string } | { v: number }): void {
  if (o instanceof Box) {
    // @skjs-expect-error Type is not assignable to the assignment target's type
    // @skjs-expect-error-line2 Type 'number | string'
    // @skjs-expect-error-line3 is not assignable to type 'number & string'
    o.v = o.v;
  }
}

// Pure queries are rejected too when the parameter names the hidden argument.
// `Map.get`/`Set.has`/`Array.includes` cannot corrupt anything -- a wrong-typed
// key just returns undefined/false -- but their declared parameter is the
// hidden type, and no value the program can produce has it. There is no way to
// recover them either: `x as Map<unknown, unknown>` is itself rejected as an
// unsound cast, in both single and double-cast form. tsc accepts all of these
// through `Map<any, any>` / `any[]`; SKJS is stricter here, not wrong, but the
// cost is real and belongs on the record rather than in the gap between
// `arrayRead`'s two element-independent reads. See issue #904.
function queryRejectedMapGet(x: unknown): void {
  if (x instanceof Map) {
    // @skjs-expect-error Argument is not assignable to the parameter's type
    // @skjs-expect-error-line2 Type '"k"'
    // @skjs-expect-error-line3 is not assignable to type 'Map#K'
    const v: unknown = x.get("k");
  }
}

function queryRejectedSetHas(x: unknown): boolean {
  if (x instanceof Set) {
    // @skjs-expect-error Argument is not assignable to the parameter's type
    // @skjs-expect-error-line2 Type '"k"'
    // @skjs-expect-error-line3 is not assignable to type 'Set#T'
    return x.has("k");
  }
  return false;
}

function queryRejectedArrayIncludes(x: unknown): boolean {
  if (x instanceof Array) {
    // @skjs-expect-error Argument is not assignable to the parameter's type
    // @skjs-expect-error-line2 Type '"k"'
    // @skjs-expect-error-line3 is not assignable to type 'Array#T'
    return x.includes("k");
  }
  return false;
}

// Returning a narrowed array at its top instantiation is rejected for the same
// reason the covariant mutable upcast `Array<number>` -> `Array<unknown>` is.
// Unlike the queries above this one has a workaround: annotate the return as
// `ReadonlyArray<unknown>` (pinned green below).
function toArrayMutable(x: unknown): unknown[] {
  if (x instanceof Array) {
    // @skjs-expect-error Type of returned value is not assignable to the function's return type
    // @skjs-expect-error-line2 Type 'unknown'
    // @skjs-expect-error-line3 is not assignable to type 'Array#T'
    // @skjs-expect-error-line4 Function parameter types are checked contravariantly: target parameter type 'unknown' must be assignable to source parameter type 'Array#T'
    return x;
  }
  return [];
}

function toArrayReadonly(x: unknown): ReadonlyArray<unknown> {
  if (x instanceof Array) {
    return x;
  }
  return [];
}

/* -------------------------------------------------------------------------
 * Hidden-type lifetimes: result, captured-state, and loop-pooling regressions.
 *
 * A skolem minted during one type-check can stand for different objects' hidden
 * arguments on different executions. An inferred result must not export that
 * shared identity. These boundary checks address the witnessed channels (#903).
 * ----------------------------------------------------------------------- */

declare function makeList<T>(): T[];

// A concrete observation may escape even when its source has a local hidden type.
function observeLocalHiddenType(x: unknown): number {
  const read = (value: unknown) => {
    if (value instanceof Tagged) return value.tag.length;
    return 0;
  };
  return read(x);
}

// An explicit opaque result does not expose the locally minted hidden type.
function opaqueHiddenResult(x: unknown): unknown {
  const reveal = (value: unknown): unknown => {
    if (value instanceof Box) return value;
    throw 0;
  };
  return reveal(x);
}

// An opaque outer container cannot expose or exchange hidden field types.
function opaqueCapturedContainer(x: unknown): unknown[] {
  const values: unknown[] = [];
  const store = (value: unknown): void => {
    if (value instanceof Box) values.push(value);
  };
  store(x);
  return values;
}

// Inference local to one invocation may use that invocation's hidden identity.
function localHiddenContainer(x: unknown): number {
  const count = (value: unknown) => {
    const values = [];
    if (value instanceof Box) values.push(value);
    return values.length;
  };
  return count(x);
}

// Repaired — inferred closure results. The arrow body is checked once, so
// every call's result is typed with the same skolem. At runtime p is
// Box<number> and q is Box<string>; the write puts a string in a
// Box<number>, and `return a.v` then yields a string from a
// number-returning function.
function holeSharedClosureResult(a: Box<number>, b: Box<string>): number {
  // @skjs-expect-error A function signature cannot expose a locally discovered hidden type; use opaque parameter and return types
  const reveal = (x: unknown) => {
    if (x instanceof Box) return x;
    throw 0;
  };
  const p = reveal(a);
  const q = reveal(b);
  p.v = q.v; // Prevented by the rejected result contract above.
  return a.v;
}

// Repaired — the higher-order face of the same sharing: generic inference
// retains the skolem in R, so one call's Pair holds two runtime-distinct
// objects under one hidden type, and results of separate calls unify too.
declare function applyTwo<R>(
  f: (x: unknown) => R,
  a: unknown,
  b: unknown,
): Pair<R, R>;
function holeHigherOrderResult(a: Box<number>, b: Box<string>): number {
  // @skjs-expect-error A function signature cannot expose a locally discovered hidden type; use opaque parameter and return types
  const reveal = (x: unknown) => {
    if (x instanceof Box) return x;
    throw 0;
  };
  const pair = applyTwo(reveal, a, b);
  pair.left.v = pair.right.v; // Prevented by the rejected result contract above.
  return a.v;
}

// Repaired — captured mutable state. The container's inferred element type
// outlives one execution of the arrow, so values stored by separate calls
// become exchangeable.
function holeCapturedContainer(a: Box<number>, b: Box<string>): number {
  const ys = makeList();
  // @skjs-expect-error A locally discovered hidden type cannot escape through an enclosing binding; give the container an opaque element type
  const store = (x: unknown): void => {
    if (x instanceof Box) {
      ys.push(x);
    }
  };
  store(a);
  store(b);
  const p = ys[0];
  const q = ys[1];
  if (p && q) {
    p.v = q.v; // Prevented by the rejected enclosing-state escape above.
  }
  return a.v;
}

// A fresh per-iteration container may infer that iteration's hidden identity.
function iterationLocalContainer(items: unknown[]): number {
  let count = 0;
  for (const value of items) {
    const local = [];
    if (value instanceof Box) local.push(value);
    count += local.length;
  }
  return count;
}

// Opaque storage can survive iterations without exposing hidden field types.
function opaqueWhileContainer(items: unknown[]): unknown[] {
  const values: unknown[] = [];
  let index = 0;
  while (index < items.length) {
    const value = items[index];
    if (value instanceof Box) values.push(value);
    index++;
  }
  return values;
}

// Hidden identities introduced by the for condition must not pool either.
function holeForConditionPooling(next: () => unknown): void {
  const values = [];
  // @skjs-expect-error A locally discovered hidden type cannot escape through an enclosing binding; give the container an opaque element type
  for (let value: unknown = next(); value instanceof Box; value = next()) {
    values.push(value);
  }
  const first = values[0];
  const second = values[1];
  if (first && second) first.v = second.v;
}

// Pooling can corrupt an earlier object before the loop exits.
function holeWhilePooling(items: unknown[]): void {
  const values = [];
  let index = 0;
  // @skjs-expect-error A locally discovered hidden type cannot escape through an enclosing binding; give the container an opaque element type
  while (index < items.length) {
    const value = items[index++];
    if (value instanceof Box) {
      values.push(value);
      const first = values[0];
      if (first) first.v = value.v;
    }
  }
}

// Repaired — pooling with nothing declared at all: no makeList, no
// closure, just the ordinary "filter a heterogeneous array" idiom. This is the
// shape that matters for judging the residual risk, because it is what a
// developer writes first. Note the inversion it creates: annotating the
// container (`const ys: Box<unknown>[] = []`) is REJECTED -- soundly, Box is
// invariant in T. Leaving it inferred now rejects the pooling at the loop
// boundary; an unknown[] annotation instead expresses safe opaque storage.
function holePureIdiom(items: unknown[]): number {
  const ys = [];
  // @skjs-expect-error A locally discovered hidden type cannot escape through an enclosing binding; give the container an opaque element type
  for (const x of items) {
    if (x instanceof Box) {
      ys.push(x);
    }
  }
  const p = ys[0];
  const q = ys[1];
  if (p && q) {
    p.v = q.v; // Prevented by the rejected loop escape above.
  }
  return ys.length;
}

// Repaired — loop bodies, no closure needed. The body is checked once, so all
// iterations share one skolem and their values pool in the outer container.
function holeLoopPooling(items: unknown[]): void {
  const ys = makeList();
  // @skjs-expect-error A locally discovered hidden type cannot escape through an enclosing binding; give the container an opaque element type
  for (const x of items) {
    if (x instanceof Box) {
      ys.push(x);
    }
  }
  const p = ys[0];
  const q = ys[1];
  if (p && q) {
    p.v = q.v; // Prevented by the rejected loop escape above.
  }
}
