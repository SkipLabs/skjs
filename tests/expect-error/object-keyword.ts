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
  // @skjs-expect-error-line3 is not assignable to type object
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

class EmptyClass {}

function objectAcceptsNonPrimitives(
  e: {},
  a: { a: number },
  f: () => void,
  arr: number[],
  c: EmptyClass,
): void {
  const o1: object = {};
  const o2: object = { a: 1 };
  const o3: object = e;
  const o4: object = a;
  const o5: object = f;
  const o6: object = arr;
  const o7: object = c;
}

// Promises are objects (stub-declared object types since #686): they satisfy
// the `object` keyword, also inside unions and intersections.
function objectAcceptsPromise(p: Promise<number>): void {
  const o1: object = p;
  const o2: object | string = p;
  const o3: object | Promise<string> = p;
}

function promiseInterObjectKeepsPromise(
  x: Promise<number> & object,
): Promise<number> {
  return x;
}

function promiseToInterObject(p: Promise<number>): Promise<number> & object {
  return p;
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
  __SKJS_show(o, `object`);
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

// --- Intersections: `string & object` is uninhabited (no value is both a
// primitive and a non-primitive), while `string & {}` collapses to `string`
// (the boxed String interface satisfies the empty object type) ---

function stringInterObjectIsUninhabited(x: string): void {
  // @ts-expect-error Type of value is not assignable to the variable's type annotation
  const so: string & object = x;
}

function stringInterObjectToNever(x: string & object): void {
  const n: never = x;
}

function objectInterFields(x: { a: number }): void {
  const o: object & { a: number } = x;
}

function objectInterFieldsBack(x: object & { a: number }): { a: number } {
  return x;
}

// The non-primitivity assertion survives intersection with fields.
function objectInterFieldsInterString(
  x: object & { a: number } & string,
): void {
  __SKJS_show(x, `never`);
}

// Unlike `object`, `{}` boxes the primitive: `string & {}` is `string`.
function stringInterEmptyCollapses(x: string & {}): void {
  __SKJS_show(x, `string`);
}

// --- keyof object is never ---

function keyofObjectIsNever(k: keyof object): void {
  const n: never = k;
}

// --- Generic constraints: T extends object ---

function expectsNonPrimitive<T extends object>(x: T): void {}

function checkConstraint(f: () => void, p: Promise<number>): void {
  expectsNonPrimitive({});
  expectsNonPrimitive({ a: 1 });
  expectsNonPrimitive(f);
  expectsNonPrimitive(p);
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
    __SKJS_show(x, `null | object`);
    // @ts-expect-error Type of value is not assignable to the variable's type annotation
    const s: string = x;
  }
}

function typeofObjectOnObject(x: object): void {
  if (typeof x === "object") {
    const o: object = x;
  } else {
    // The else branch is never, matching tsc — even though a function value
    // (typeof "function") would land here at runtime.
    const n: never = x;
  }
}

function typeofStringOnObject(x: object): void {
  if (typeof x === "string") {
    const n: never = x;
  }
}

// Functions are valid `object` values, so typeof === "function" keeps the
// `object` type on both sides (tsc narrows the matching side to `Function`,
// which SKJS cannot express; `object` is the sound over-approximation).
function typeofFunctionOnObject(x: object): void {
  if (typeof x === "function") {
    const o: object = x;
    // @ts-expect-error Type of value is not assignable to the variable's type annotation
    const n: never = x;
  } else {
    const o: object = x;
  }
}

// --- typeof narrowing and structural object types: the runtime check proves
// the surviving branch is non-primitive ---

// A narrowed {} is exactly the `object` keyword: the runtime check proved
// non-primitivity and {} imposes no structural demands.
function typeofObjectOnEmpty(e: {}): void {
  if (typeof e === "object") {
    __SKJS_show(e, `object`);
  }
}

function typeofObjectProvesNonPrimitive(
  x: { length: number } | string,
  s: string,
): void {
  if (typeof x === "object") {
    __SKJS_show(x, `{ length: number }`);
    // @skjs-expect-warning This comparison is always false because the operand types do not overlap
    if (x === s) {
      // x was proven non-primitive by the typeof check, so it cannot equal a
      // string: the equality intersection is uninhabited (without the proof,
      // the boxed String interface would satisfy { length: number }).
      __SKJS_show(x, `never`);
    }
  }
}

function typeofFunctionProvesNonPrimitive(f: (() => void) | string): void {
  if (typeof f === "function") {
    __SKJS_show(f, `() => void`);
  }
}

// Joining a typeof-proven branch with an unmarked branch of the same shape
// keeps two clauses that render identically (known cosmetic quirk: the
// proven branch narrows differently, e.g. to never against === string, so
// the clauses are genuinely distinct — only their printed forms collide).
function joinProvenAndUnknown(
  x: { length: number } | string,
  y: { length: number },
  c: boolean,
): void {
  if (typeof x === "object") {
    const z = c ? x : y;
    __SKJS_show(z, `{ length: number } | { length: number }`);
  }
}

// Functions inhabit `{}` (it imposes no demands), so its
// typeof === "function" part is "all functions" — the bare non-primitive
// branch, i.e. `object` (tsc narrows to Function, which SKJS cannot
// express).
function typeofFunctionOnEmpty(e: {}): void {
  if (typeof e === "function") {
    __SKJS_show(e, `object`);
  }
}

// The comparison is provably always false: o is non-primitive, so no string
// can box into it. The equality narrowing yields never and the comparison
// warns.
function objectComparedToString(o: object, s: string): void {
  // @skjs-expect-warning This comparison is always false because the operand types do not overlap
  if (o === s) {
    __SKJS_show(o, `never`);
  }
}

// --- for...in over `object` ---

function forInOverObject(o: object): void {
  for (const k in o) {
    const s: string = k;
  }
}
