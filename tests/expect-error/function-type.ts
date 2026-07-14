///////////////////////////////////////////////////////////////////////////////
// The global `Function` type: definitely callable, unknown signature
// (issue #805).
//
// `Function` proves its inhabitants implement [[Call]] without offering a
// signature, so it accepts exactly the values that prove callability
// (functions, class constructors, construct-signature values) and is itself
// not invocable.
///////////////////////////////////////////////////////////////////////////////

class C {
  a: number = 1;
}

class Empty {}

// A plain function is assignable to Function.
function testFnToFunction(f: () => void): Function {
  return f;
}

// A class-constructor value is assignable to Function (it implements
// [[Call]] even though invoking it without `new` throws).
function testCtorToFunction(): Function {
  return C;
}

// A construct-signature value is assignable to Function.
function testNewSigToFunction(o: { new (): C }): Function {
  return o;
}

// An unknown-callability object is NOT assignable to Function: nothing
// launders into the positive brand (tsc rejects too, TS2740).
function testEmptyToFunction(o: {}): Function {
  // @ts-expect-error Type of returned value is not assignable to the function's return type
  return o;
}

// A class instance is NOT assignable to Function.
function testInstanceToFunction(c: C): Function {
  // @ts-expect-error Type of returned value is not assignable to the function's return type
  return c;
}

// Neither is an array.
function testArrayToFunction(xs: number[]): Function {
  // @ts-expect-error Type of returned value is not assignable to the function's return type
  return xs;
}

// Function is assignable to the empty object type.
function testFunctionToEmpty(f: Function): {} {
  return f;
}

// Function is not assignable to a specific call signature.
function testFunctionToFn(f: Function): () => void {
  // @ts-expect-error Type of returned value is not assignable to the function's return type
  return f;
}

// Function is not assignable to a class-instance type. Stricter than tsc,
// which accepts the empty-instance target structurally and then unsoundly
// narrows it to never in the typeof-"function" branch a stored function
// makes reachable.
function testFunctionToEmptyClass(f: Function): Empty {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return f;
}

// A Function-typed value is not invocable: its signature is unknown, so a
// call cannot be checked. Stricter than tsc, which allows the call at an
// implicit any type.
function testFunctionNotInvocable(f: Function): void {
  // @skjs-expect-error This expression is not callable
  // @skjs-expect-error-line2 Type 'Function' is callable, but its signature is unknown
  f();
}

// ... and not constructible (tsc agrees, TS2351).
function testFunctionNotConstructable(f: Function): void {
  // @ts-expect-error This expression is not constructable
  const x = new f();
}

// typeof narrowing: Function is definitely typeof "function".
function testFunctionTypeofFunction(f: Function): void {
  if (typeof f === "function") {
  } else {
    const n: never = f;
  }
}

function testFunctionTypeofObject(f: Function): void {
  if (typeof f === "object") {
    const n: never = f;
  }
}

// A Function-typed value is a valid instanceof right-hand side.
function testFunctionInstanceofRhs(f: Function, x: unknown): void {
  if (x instanceof f) {
  }
}

// A Function-typed condition reports the generic truthiness restriction,
// deliberately not the always-true diagnostic: TS2774 is the forgot-to-call
// heuristic, and a Function value is not invocable, so it cannot be a
// forgotten call.
function testFunctionTruthiness(f: Function): void {
  // @skjs-expect-error A condition is expected to be of type boolean or a type with a single falsy value
  if (f) {
  }
}

// FIXME(#806): a type parameter is not narrowed by typeof === "function":
// the true branch keeps x at T, so the runtime proof is unusable. tsc
// narrows to T & Function and accepts the return.
function testTParamTypeofFunction<T>(x: T): Function {
  if (typeof x === "function") {
    // @skjs-expect-error Type of returned value is not assignable to the function's return type
    return x;
  }
  return () => {};
}

// FIXME(#806): same for unknown — the true branch keeps x at unknown. tsc
// narrows to Function.
function testUnknownTypeofFunction(x: unknown): Function {
  if (typeof x === "function") {
    // @skjs-expect-error Type of returned value is not assignable to the function's return type
    return x;
  }
  return () => {};
}

// An interface extending Function inherits provable callability, and a
// plain function satisfies it structurally.
interface Callback extends Function {}

function testFnToCallbackInterface(g: () => number): Callback {
  return g;
}
