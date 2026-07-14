///////////////////////////////////////////////////////////////////////////////
// The global `Function` type: definitely callable, unknown signature
// (issue #805).
//
// FIXME: `Function` is not declared by the import stubs yet; every reference
// below currently fails to resolve. tsc resolves all of them. The pins flip
// to real assertions once the stub and its Callability state land.
///////////////////////////////////////////////////////////////////////////////

class C {
  a: number = 1;
}

// A plain function is assignable to Function.
// @skjs-expect-error Cannot find type 'Function'
function testFnToFunction(f: () => void): Function {
  return f;
}

// A class-constructor value is assignable to Function (it implements
// [[Call]] even though invoking it without `new` throws).
// @skjs-expect-error Cannot find type 'Function'
function testCtorToFunction(): Function {
  return C;
}

// A construct-signature value is assignable to Function.
// @skjs-expect-error Cannot find type 'Function'
function testNewSigToFunction(o: { new (): C }): Function {
  return o;
}

// An unknown-callability object is NOT assignable to Function (tsc rejects
// with TS2740).
// @skjs-expect-error Cannot find type 'Function'
function testEmptyToFunction(o: {}): Function {
  return o;
}

// A class instance is NOT assignable to Function.
// @skjs-expect-error Cannot find type 'Function'
function testInstanceToFunction(c: C): Function {
  return c;
}

// Function is assignable to the empty object type.
// @skjs-expect-error Cannot find type 'Function'
function testFunctionToEmpty(f: Function): {} {
  return f;
}

// Function is not assignable to a specific call signature.
// @skjs-expect-error Cannot find type 'Function'
function testFunctionToFn(f: Function): () => void {
  return f;
}

// A Function-typed value is not invocable: its signature is unknown, so a
// call cannot be checked. Stricter than tsc, which allows the call at an
// implicit any type.
// @skjs-expect-error Cannot find type 'Function'
function testFunctionNotInvocable(f: Function): void {
  f();
}

// ... and not constructible (tsc agrees, TS2351).
// @skjs-expect-error Cannot find type 'Function'
function testFunctionNotConstructable(f: Function): void {
  const x = new f();
}

// typeof narrowing: Function is definitely typeof "function".
// @skjs-expect-error Cannot find type 'Function'
function testFunctionTypeofFunction(f: Function): void {
  if (typeof f === "function") {
  } else {
    const n: never = f;
  }
}

// @skjs-expect-error Cannot find type 'Function'
function testFunctionTypeofObject(f: Function): void {
  if (typeof f === "object") {
    const n: never = f;
  }
}

// A Function-typed value is a valid instanceof right-hand side.
// @skjs-expect-error Cannot find type 'Function'
function testFunctionInstanceofRhs(f: Function, x: unknown): void {
  if (x instanceof f) {
  }
}

// An interface extending Function inherits provable callability, and a
// plain function satisfies it structurally.
// @skjs-expect-error Cannot find type 'Function'
interface Callback extends Function {}

function testFnToCallbackInterface(g: () => number): Callback {
  return g;
}
