// Tests for the Promise<T> surface: method access, subtyping variance,
// await, `in`, `keyof`, type-argument arity, and async return-type
// validation.

// FIXME: tsc types `.then`/`.catch`/`.finally` via the Promise lib; SKJS does
// not yet expose Promise methods.
function testThen(p: Promise<number>): Promise<string> {
  // @skjs-expect-error Property access is not allowed on this type
  return p.then((n) => n.toString());
}

function testCatch(p: Promise<number>): Promise<number> {
  // @skjs-expect-error Property access is not allowed on this type
  return p.catch((reason) => 0);
}

function testFinally(p: Promise<number>): Promise<number> {
  // @skjs-expect-error Property access is not allowed on this type
  return p.finally(() => {});
}

// Promise is covariant in its payload.
function testCovariantNever(p: Promise<never>): Promise<number> {
  return p;
}

function testCovariantWiden(p: Promise<number>): Promise<number | string> {
  return p;
}

function testCovariantBad(p: Promise<number | string>): Promise<number> {
  // @ts-expect-error Type of returned value is not assignable to the function's return type
  return p;
}

// await unwraps one level of Promise.
async function testAwait(p: Promise<number>): Promise<number> {
  return await p;
}

async function testAwaitUnion(
  b: boolean,
  p1: Promise<number>,
  p2: Promise<string>,
): Promise<number | string> {
  const p = b ? p1 : p2;
  return await p;
}

interface Thenable {
  then<U>(onfulfilled: (value: number) => U | Promise<U>): Promise<U>;
}

// FIXME: tsc unwraps any structurally well-shaped thenable in `await`; SKJS
// requires a Promise.
async function testAwaitThenable(t: Thenable): Promise<number> {
  // @skjs-expect-error 'await' can only be applied to a Promise
  return await t;
}

// FIXME: tsc accepts: Promise<number> is structurally a thenable.
function testPromiseIsThenable(p: Promise<number>): Thenable {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return p;
}

// Error: awaiting a non-thenable value. (tsc lets `await` pass non-thenables
// through; SKJS intentionally rejects, like @typescript-eslint/await-thenable.)
async function testAwaitNumber(n: number): Promise<number> {
  // @skjs-expect-error 'await' can only be applied to a Promise
  return await n;
}

async function testAwaitPlainObject(o: { a: number }): Promise<number> {
  // @skjs-expect-error 'await' can only be applied to a Promise
  const r = await o;
  return r.a;
}

// FIXME: tsc flattens nested thenables: `await p` is number there, and async
// return statements compare awaited types, so tsc accepts both functions
// below. SKJS unwraps exactly one level and rejects testAwaitNestedFlat.
async function testAwaitNested(
  p: Promise<Promise<number>>,
): Promise<Promise<number>> {
  return await p;
}

async function testAwaitNestedFlat(
  p: Promise<Promise<number>>,
): Promise<number> {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return await p;
}

// FIXME: tsc supports `in` on promises; SKJS does not yet.
function testIn(p: Promise<number>): boolean {
  // @skjs-expect-error The 'in' operator is not yet supported by SKJS for this type
  return "then" in p;
}

// FIXME: tsc supports `keyof` on promises; SKJS does not yet.
// @skjs-expect-error 'keyof' is not yet supported by SKJS for type Promise<number>
function testKeyof(k: "then" | "catch" | "finally"): keyof Promise<number> {
  return k;
}

// Error: Promise takes exactly one type argument.
// @ts-expect-error Expected 1 type arguments, but got 2 (Promise<T> requires exactly one)
function testArityTwo(p: Promise<number, string>): void {}

// @ts-expect-error Expected 1 type arguments, but got 0 (Promise<T> requires exactly one)
function testArityZero(p: Promise): void {}

// Error: an async function's return type must be the global Promise type,
// even for structurally well-shaped thenables.
// @ts-expect-error The return type of an async function must be the global Promise<T> type
async function testAsyncRetNumber(): number {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return 0;
}

// @ts-expect-error The return type of an async function must be the global Promise<T> type
async function testAsyncRetUnion(): Promise<number> | undefined {
  return 0;
}

// @ts-expect-error The return type of an async function must be the global Promise<T> type
async function testAsyncRetThenable(): Thenable {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return 0;
}

// Async functions returning Promise<void> need no return statement.
async function testAsyncVoid(): Promise<void> {}

// @ts-expect-error Not all code paths return a value, and the return type does not include 'undefined'
async function testAsyncMissingReturn(): Promise<number> {}
