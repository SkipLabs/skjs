// Tests for the Promise<T> surface: method access, subtyping variance,
// await, `in`, `keyof`, type-argument arity, and async return-type
// validation.

function testThen(p: Promise<number>): Promise<string> {
  return p.then((n: number) => n.toString());
}

// A callback returning Promise<U> also produces Promise<U> (then flattens).
function testThenChained(p: Promise<number>): Promise<string> {
  return p.then((n: number) => p.then((m: number) => m.toString()));
}

function testCatch(p: Promise<number>): Promise<number> {
  return p.catch((reason: unknown) => 0);
}

function testFinally(p: Promise<number>): Promise<number> {
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

// `await` on a union that is only partly a promise: a non-fatal error, and
// checking continues with the awaited type of the promise branches only.
// (tsc reports nothing and types the result with the non-thenable parts
// passed through, e.g. number | { a: number } below where SKJS uses number.)
async function testAwaitPartialPromise(
  b: boolean,
  p: Promise<number>,
  n: number,
): Promise<number> {
  const x = b ? p : n;
  // @skjs-expect-error 'await' can only be applied to a Promise
  return await x;
}

async function testAwaitPartialPromiseMismatch(
  b: boolean,
  p: Promise<number>,
  s: string,
): Promise<string> {
  const x = b ? p : s;
  // Checking continues past the non-fatal await error with the awaited type
  // of the promise branches only (number here), so the return mismatch is
  // also reported.
  // @skjs-expect-error 'await' can only be applied to a Promise
  // @ts-expect-error Type of returned value is not assignable to the function's return type
  return await x;
}

async function testAwaitPartialThenableObject(
  b: boolean,
  p: Promise<number>,
  o: { a: number },
): Promise<number> {
  const x = b ? p : o;
  // @skjs-expect-error 'await' can only be applied to a Promise
  return await x;
}

interface Thenable {
  then<U>(onfulfilled: (value: number) => U | Promise<U>): Promise<U>;
}

// FIXME: tsc declares PromiseLike<T> in its lib; the SKJS stubs do not yet.
// @skjs-expect-error Cannot find type 'PromiseLike'
function testPromiseIsPromiseLike(p: Promise<number>): PromiseLike<number> {
  return p;
}

// `await` unwraps any structurally well-shaped thenable, like tsc.
async function testAwaitThenable(t: Thenable): Promise<number> {
  return await t;
}

// Promise<number> is structurally a thenable.
function testPromiseIsThenable(p: Promise<number>): Thenable {
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

// `then` is a required field of every Promise, so the check is always true
// (tsc does not report this).
function testIn(p: Promise<number>): boolean {
  // @skjs-expect-error This condition is always true
  return "then" in p;
}

function testKeyof(k: "then" | "catch" | "finally"): keyof Promise<number> {
  return k;
}

// Error: Promise takes exactly one type argument.
// @ts-expect-error Expected 1 type arguments, but got 2
function testArityTwo(p: Promise<number, string>): void {}

// @ts-expect-error Expected 1 type arguments, but got 0
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
  return 0;
}

// Async functions returning Promise<void> need no return statement.
async function testAsyncVoid(): Promise<void> {}

// @ts-expect-error Not all code paths return a value, and the return type does not include 'undefined'
async function testAsyncMissingReturn(): Promise<number> {}
