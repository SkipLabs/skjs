///////////////////////////////////////////////////////////////////////////////
// Callability modes: how object types track call/construct capability, and
// how `typeof x === "function"` / `typeof x === "object"` narrowing and
// assignability consume it (issue #774).
//
// Runtime ground truth (ECMA-262): `typeof v === "function"` iff v implements
// [[Call]]; every constructible value implements [[Call]] (a class constructor
// is typeof "function" even though invoking it without `new` throws).
///////////////////////////////////////////////////////////////////////////////

class C {
  a: number = 1;
}

class Empty {}

interface Iface {
  b: number;
}

///////////////////////////////////////////////////////////////////////////////
// Class-constructor values under typeof (issue #774)
///////////////////////////////////////////////////////////////////////////////

// FIXME: A class-constructor value is typeof "function" at runtime, but SKJS
// drops it from the true branch (narrows F to never), so the unsound
// assignment below is accepted. tsc rejects it (TS2322). Issue #774.
function testCtorTypeofFunction(): string {
  const F = C;
  if (typeof F === "function") {
    const s: string = F;
    return s;
  }
  return "not a function";
}

// FIXME: The dual bug: `typeof F === "object"` is always false for a
// constructor value, so at runtime the else branch is taken — but SKJS
// narrows F to never there and accepts the never-assignment. tsc keeps F as
// `typeof C` in the else branch and rejects. Issue #774.
function testCtorTypeofObjectElse(): void {
  const F = C;
  if (typeof F === "object") {
  } else {
    const n: never = F;
  }
}

// A constructor value is not invocable without `new`, and must stay that way
// even once typeof narrowing keeps it in the "function" branch.
function testCtorNotInvocable(): void {
  const F = C;
  // @ts-expect-error This expression is not callable
  F();
}

function testCtorNew(): C {
  const F = C;
  return new F();
}

// A construct signature does not provide a call signature: tsc rejects with
// TS2322 ("provides no match for the signature").
function testCtorToFnRejected(): () => C {
  // @ts-expect-error Type of returned value is not assignable to the function's return type
  return C;
}

// A constructor value satisfies a construct-signature object type.
function testCtorToNewSig(): { new (): C } {
  return C;
}

// FIXME: A `{ new (): C }`-typed value is constructible, hence typeof
// "function" at runtime, but SKJS drops it from the true branch. tsc keeps it
// (narrows to `new () => C`) and rejects the never-assignment.
function testNewSigTypeofFunction(o: { new (): C }): void {
  if (typeof o === "function") {
    const n: never = o;
  }
}

///////////////////////////////////////////////////////////////////////////////
// Unknown callability: structural object types admit callable inhabitants
///////////////////////////////////////////////////////////////////////////////

// FIXME: `{}` admits callable inhabitants (`const o: {} = () => {}` is
// accepted right below), so narrowing it to never in the "function" branch is
// unsound. tsc keeps it (as Function) and rejects the never-assignment.
function testEmptyTypeofFunction(o: {}): void {
  if (typeof o === "function") {
    const n: never = o;
  }
}

// FIXME: The dual: a function stored in a `{}`-typed variable makes the else
// branch of `typeof o === "object"` reachable, but SKJS narrows o to never
// there. tsc keeps `{}` and rejects the never-assignment.
function testEmptyTypeofObjectElse(o: {}): void {
  if (typeof o === "object") {
  } else {
    const n: never = o;
  }
}

// Width subtyping: a function is assignable to the empty object type.
function testFnToEmptyObject(f: () => void): {} {
  return f;
}

// A function with matching extra properties inhabits `{ a: number }`
// (e.g. Object.assign(function () {}, { a: 1 })), so narrowing the true
// branch to never claims emptiness of an inhabited branch. tsc shares this
// unsoundness (it also narrows to never here); SKJS currently matches it.
function testPropsTypeofFunction(o: { a: number }): void {
  if (typeof o === "function") {
    const n: never = o;
  }
}

// Same for interface types: nothing prevents a callable inhabitant.
function testInterfaceTypeofFunction(o: Iface): void {
  if (typeof o === "function") {
    const n: never = o;
  }
}

///////////////////////////////////////////////////////////////////////////////
// Definite non-callability: class instances and arrays keep precise narrowing
///////////////////////////////////////////////////////////////////////////////

// A class instance is not callable: the "function" branch is never.
function testInstanceTypeofFunction(c: C): void {
  if (typeof c === "function") {
    const n: never = c;
  }
}

// Arrays (mutable and readonly) are never callable: the "function" branch is
// never.
function testArrayTypeofFunction(xs: number[]): void {
  if (typeof xs === "function") {
    const n: never = xs;
  }
}

function testReadonlyArrayTypeofFunction(xs: readonly number[]): void {
  if (typeof xs === "function") {
    const n: never = xs;
  }
}

///////////////////////////////////////////////////////////////////////////////
// Assignability of functions to class-instance types
///////////////////////////////////////////////////////////////////////////////

// A function is currently assignable to an empty class-instance type (tsc
// also accepts). This is the direct inflow that makes the class-instance
// never-narrowing above unsound: testInstanceTypeofFunction's reasoning only
// holds if known-callable values cannot flow into instance-typed slots.
function testFnToEmptyClass(f: () => void): Empty {
  return f;
}

// Structural assignability into class-instance types (unaffected: an object
// with unknown callability may flow into an instance-typed slot).
function testStructuralToClass(o: { a: number }): C {
  return o;
}

function testLiteralToClass(): C {
  return { a: 1 };
}

///////////////////////////////////////////////////////////////////////////////
// Callable objects with properties
///////////////////////////////////////////////////////////////////////////////

// A hybrid intersection (callable with properties) stays callable and keeps
// its fields.
function testHybridIntersection(h: (() => void) & { a: number }): number {
  h();
  return h.a;
}

// Union of a callable and a plain object type: SKJS currently drops the
// object arm in the "function" branch (like tsc), so the call typechecks.
// This is unsound — a function with an `a` property inhabits the second arm
// with an unrelated signature — but it is pinned here as current behavior.
function testUnionCallbackCall(x: (() => string) | { a: number }): void {
  if (typeof x === "function") {
    const s: string = x();
  }
}
