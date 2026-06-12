// Tests for the `object` keyword type (issue #674). In TypeScript, `object`
// means "any non-primitive value": everything except string, number, bigint,
// boolean, symbol, null and undefined. Functions, arrays and class instances
// are all `object`. It is NOT the same type as `{}`, which in TypeScript also
// accepts primitives (SKJS deliberately rejects primitives for `{}` too, see
// below).

// --- Assignability to `object`: primitives and nullish are rejected ---

function objectRejectsString(x: string): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  // @skjs-expect-error-line2 Type string
  // @skjs-expect-error-line3 is not assignable to type {  }
  const o: object = x;
}

function objectRejectsNumber(x: number): void {
  // @ts-expect-error Type of value is not assignable to the variable's type annotation
  const o: object = x;
}

function objectRejectsNull(x: null): void {
  // @ts-expect-error Type of value is not assignable to the variable's type annotation
  const o: object = x;
}

function objectRejectsUndefined(x: undefined): void {
  // @ts-expect-error Type of value is not assignable to the variable's type annotation
  const o: object = x;
}

function objectRejectsPrimitiveUnion(x: string | number): void {
  // @ts-expect-error Type of value is not assignable to the variable's type annotation
  const o: object = x;
}

function objectRejectsUnknown(x: unknown): void {
  // @ts-expect-error Type of value is not assignable to the variable's type annotation
  const o: object = x;
}

// --- Assignability to `object`: non-primitives are accepted ---

function objectAcceptsNonPrimitives(
  e: {},
  a: { a: number },
  f: () => void,
  arr: number[],
): void {
  const o1: object = {};
  const o2: object = { a: 1 };
  const o3: object = e;
  const o4: object = a;
  const o5: object = f;
  const o6: object = arr;
}

// Promises are objects (stub-declared object types since #686).
function objectAcceptsPromise(p: Promise<number>): void {
  const o: object = p;
}

// --- Assignability from `object` ---

function objectAssignableToEmpty(o: object): {} {
  return o;
}

function objectAssignableToUnknown(o: object): unknown {
  return o;
}

function objectNotAssignableToFields(o: object): { a: number } {
  // @ts-expect-error Type of returned value is not assignable to the function's return type
  return o;
}

// --- Printing: the `object` keyword's printed form ---

function objectPrinting(o: object): void {
  __SKJS_show(o, `{  }`);
}

// --- SKJS's `{}` also rejects primitives (deliberate, stricter than tsc) ---
// In TypeScript primitives are assignable to `{}` via apparent (boxed)
// members; SKJS has no boxing in assignability, which keeps width subtyping
// sound. This makes SKJS's `{}` behave like `object` for assignability; the
// two types still differ in printing, intersections and narrowing.

function emptyObjectTypeRejectsString(x: string): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const e: {} = x;
}

// --- Intersections: in TypeScript `string & object` is uninhabited (no value
// is both a primitive and a non-primitive) ---

// FIXME: tsc rejects this (`string & object` reduces to never); SKJS
// currently collapses `string & object` to `string`.
function stringInterObjectIsUninhabited(x: string): void {
  const so: string & object = x;
}

// FIXME: tsc accepts this (`string & object` is never); SKJS currently
// collapses `string & object` to `string`.
function stringInterObjectToNever(x: string & object): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const n: never = x;
}

function objectInterFields(x: { a: number }): void {
  const o: object & { a: number } = x;
}

function objectInterFieldsBack(x: object & { a: number }): { a: number } {
  return x;
}

// --- keyof object is never ---

function keyofObjectIsNever(k: keyof object): void {
  const n: never = k;
}

// --- Generic constraints: T extends object ---

function expectsNonPrimitive<T extends object>(x: T): void {}

function checkConstraint(f: () => void): void {
  expectsNonPrimitive({});
  expectsNonPrimitive({ a: 1 });
  expectsNonPrimitive(f);
  // @ts-expect-error Argument is not assignable to the parameter's type
  expectsNonPrimitive("hello");
}

// --- Property access on `object` ---

function objectHasNoProperties(o: object): void {
  // @ts-expect-error Property 'foo' does not exist on this type
  const v = o.foo;
}

// In TypeScript, Object.prototype members (toString, hasOwnProperty, ...) are
// accessible on `object` via the apparent type. SKJS has no apparent-type
// machinery and objects created with Object.create(null) lack these members,
// so allowing them would be unsound; SKJS rejects (deliberate).
function objectHasNoPrototypeMembers(o: object): void {
  // @skjs-expect-error Property 'toString' does not exist on this type
  const s = o.toString;
}

// --- typeof narrowing ---

function typeofObjectOnUnknown(x: unknown): void {
  if (typeof x === "object") {
    const o: object | null = x;
    // @ts-expect-error Type of value is not assignable to the variable's type annotation
    const s: string = x;
  }
}

function typeofObjectOnObject(x: object): void {
  if (typeof x === "object") {
    const o: object = x;
  } else {
    const n: never = x;
  }
}

function typeofStringOnObject(x: object): void {
  if (typeof x === "string") {
    const n: never = x;
  }
}

// FIXME: tsc narrows `object` to `Function` here, so `const n: never = x`
// is an error in tsc; SKJS currently narrows `object` under
// typeof === "function" to `never`, which is unsound (functions are valid
// `object` values).
function typeofFunctionOnObject(x: object): void {
  if (typeof x === "function") {
    const n: never = x;
  }
}

// --- for...in over `object` ---

function forInOverObject(o: object): void {
  for (const k in o) {
    const s: string = k;
  }
}
