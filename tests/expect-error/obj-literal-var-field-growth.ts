// A fresh object literal's field whose value is a plain variable reference is
// routed through a growable field type variable (like object, closure, and
// primitive values already were), so the variable's narrowed type can widen to
// the declared field type. The variable stays a live alias of the stored
// object, and growth keeps its type as a lower bound checked against the
// declared field type with full invariant-interior subtyping — the slot admits
// no interior write the alias's own type does not already permit. These pins
// hold the guards that keep that sound.

type ListNum = null | { head: number; tail: ListNum };

// The motivating case: a recursive structure built by reassigning an annotated
// local. The variable's narrowed type equals the target branch after its own
// embedded field variables grow.
function recursiveBuild(x: number): ListNum {
  let result: ListNum = null;
  result = { head: x, tail: null };
  result = { head: x, tail: result };
  return result;
}

// The canonical attack stays rejected: the variable's concrete interior is
// narrower than the target field type, and widening the slot would let
// `o.a.x = 99` corrupt `e.x` while it is still read at type `1`. tsc accepts
// this via its unsound mutable-property covariance; SKJS must not.
function interiorNarrowerRejected(): void {
  const e: { x: 1 } = { x: 1 };
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const o: { a: { x: number } } = { a: e };
  void o;
}

// A type-parameter-typed value grows too: inside the body, X's mutable fields
// are exactly the bound's (instantiation is invariant), so the slot's write
// vocabulary adds nothing.
function tparamGrows<X extends { x: number }>(v: X): void {
  const o: { a: { x: number } } = { a: v };
  o.a.x = 99;
}

// ...and the invariant instantiation check is the guard that keeps it sound:
// a narrower-interior type argument cannot enter. tsc accepts this call.
function tparamInstantiationGuard(): void {
  const e: { x: 1 } = { x: 1 };
  // @skjs-expect-error Argument is not assignable to the parameter's type
  tparamGrows(e);
}

// A concrete variable grows into a union-typed slot when it equals one branch.
// Sound because a member write through the union view must satisfy every
// branch (meet), so the alias's branch cannot be corrupted — the rejected
// write below is the guard.
function unionSlotGrows(): void {
  const e: { tag: "a"; n: number } = { tag: "a", n: 1 };
  const o: { u: { tag: "a"; n: number } | { tag: "b"; s: string } } = { u: e };
  // @skjs-expect-error Type is not assignable to the assignment target's type
  o.u.tag = "b";
}

// A variable with a required field grows into a slot where that field is
// optional. Sound today only because optional fields are exact (present => T,
// so `o.a.y = undefined` is rejected) and `delete` is unsupported; if either
// changes, this acceptance becomes a hole (delete `e.y` through the optional
// view) and must be revisited.
function requiredToOptionalGrows(): void {
  const e: { x: number; y: string } = { x: 1, y: "keep" };
  const o: { a: { x: number; y?: string } } = { a: e };
  void o;
}

function storedObjectAlias(x: { f: number | null }): number {
  if (x.f !== null) {
    // A fresh outer slot does not stabilize its aliased contents.
    const box = { value: x };
    x.f = null;
    // @ts-expect-error Type of returned value is not assignable to the function's return type
    return box.value.f;
  }
  return 0;
}

function computedObjectAlias(x: { f: number | null }, key: "value"): number {
  // Computed slots retain the conditional's stable contract.
  const box = { [key]: x.f !== null ? x : { f: 0 } };
  x.f = null;
  // @ts-expect-error Type of returned value is not assignable to the function's return type
  return box.value.f;
}

// Scalar spreading copies values; mutating the source cannot change the copy.
// TypeScript rejects this safe read because it does not narrow the spread field.
function copiedObjectField(x: { f: number | null }): number {
  if (x.f !== null) {
    const box = { ...x };
    x.f = null;
    return box.f;
  }
  return 0;
}

function keyClearsRhs(x: number | null): number {
  if (x === null) return 0;
  const box = { slot: 0 };
  const before: number = box.slot;
  // FIXME: the key clears x before the right-hand side is evaluated.
  box[(x = null) === null ? "slot" : "slot"] = x;
  return box.slot;
}
function keyInitializesRhs(): number {
  // FIXME: the key initializes x before the right-hand side is evaluated.
  // @skjs-expect-error Type is not assignable to the field's type
  let x: number | null = null;
  const box = { slot: 0 };
  const before: number = box.slot;
  box[(x = 1) === 1 ? "slot" : "slot"] = x;
  return box.slot;
}
