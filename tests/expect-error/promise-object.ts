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
// checking continues with the thenable branches unwrapped and the
// non-thenable parts passed through, exactly as the runtime behaves (and as
// tsc types the result — tsc just reports nothing).
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
  // The continuation type is number | string, so the return mismatch is
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
  // The continuation type is number | { a: number }, like tsc's.
  // @skjs-expect-error 'await' can only be applied to a Promise
  // @ts-expect-error Type of returned value is not assignable to the function's return type
  return await x;
}

// Promise<number> is structurally a PromiseLike<number>.
function testPromiseIsPromiseLike(p: Promise<number>): PromiseLike<number> {
  return p;
}

// `await` unwraps any structurally well-shaped thenable, like tsc and like
// JavaScript (the runtime calls `then` on whatever it gets).
async function testAwaitThenable(t: PromiseLike<number>): Promise<number> {
  return await t;
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

// FIXME: tsc accepts: a thenable wrapping a promise awaits to number
// (recursive flattening); SKJS unwraps exactly one level.
async function testAwaitThenableNested(
  t: PromiseLike<Promise<number>>,
): Promise<number> {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return await t;
}

// FIXME: tsc rejects self-referential thenables with TS1062 ("Type is
// referenced directly or indirectly in the fulfillment callback of its own
// 'then' method") at async declarations, async returns, async arrow bodies,
// and await expressions; SKJS accepts all four shapes below.
interface SelfThen {
  then(onfulfilled: (value: SelfThen) => void): SelfThen;
}

async function testAwaitSelfThenable(s: SelfThen): Promise<SelfThen> {
  return await s;
}

async function testAsyncReturnSelfThenable(s: SelfThen): Promise<SelfThen> {
  return s;
}

async function testAwaitIndirectSelfThenable(
  p: Promise<SelfThen>,
): Promise<number> {
  const x = await p;
  return 0;
}

function testArrowSelfThenable(s: SelfThen): () => Promise<SelfThen> {
  return async () => s;
}

// FIXME: tsc accepts returning a promise from an async function (return
// expressions are compared by awaited type there); SKJS wraps the promise
// into a nested promise and rejects all three shapes below.
async function testAsyncReturnPromise(p: Promise<number>): Promise<number> {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return p;
}

function testArrowReturnPromise(p: Promise<number>): () => Promise<number> {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return async () => p;
}

function testBlockArrowReturnPromise(
  p: Promise<number>,
): () => Promise<number> {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return async () => {
    return p;
  };
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
async function testAsyncRetThenable(): PromiseLike<number> {
  // The body is still checked against the annotation; no error here because
  // `return 0` wraps to Promise<'0'>, which is assignable to
  // PromiseLike<number> (unlike testAsyncRetNumber's annotation above).
  return 0;
}

// Async functions returning Promise<void> need no return statement.
async function testAsyncVoid(): Promise<void> {}

// @ts-expect-error Not all code paths return a value, and the return type does not include 'undefined'
async function testAsyncMissingReturn(): Promise<number> {}
