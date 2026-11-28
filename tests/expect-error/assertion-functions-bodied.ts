// Bodied assertion functions (`asserts x`, `asserts x is T`, `asserts this`,
// `asserts this is T`) — issue #583.
//
// Every normal return path (explicit `return` and implicit fallthrough) must
// soundly prove the asserted postcondition.

// --- 1. Valid bodied `asserts x is T` and `asserts x` functions ---

function assertStr(x: unknown): asserts x is string {
  if (typeof x !== "string") {
    throw new Error("not string");
  }
}

function useAssertStr(x: string | number): string {
  assertStr(x);
  return x;
}

function assertTruthyBool(x: boolean): asserts x {
  if (!x) {
    throw new Error("falsy");
  }
}

function useAssertTruthyBool(x: string | number): string {
  assertTruthyBool(typeof x === "string");
  return x;
}

function assertTruthyObj(x: { readonly a: number } | null): asserts x {
  if (!x) {
    throw new Error("null");
  }
}

function useAssertTruthyObj(x: { readonly a: number } | null): number {
  assertTruthyObj(x);
  return x.a;
}

function assertTruthyZeroOrOne(x: 0 | 1): asserts x {
  if (x === 0) {
    throw new Error("zero");
  }
}

function useAssertTruthyZeroOrOne(x: 0 | 1): 1 {
  assertTruthyZeroOrOne(x);
  return x;
}

function assertDefined<T>(x: T | null | undefined): asserts x is T {
  if (x === null || x === undefined) {
    throw new Error("nullish");
  }
}

function useAssertDefined(x: number | null | undefined): number {
  assertDefined(x);
  return x;
}

// Early `return;` and `return undefined;` after proving the postcondition.
function assertEarlyReturn(x: unknown): asserts x is string {
  if (typeof x === "string") {
    return;
  }
  throw new Error("not string");
}

function assertReturnUndefined(x: unknown): asserts x is string {
  if (typeof x === "string") {
    return undefined;
  }
  throw new Error("not string");
}

// Non-first parameter.
function assertSecond(label: string, x: unknown): asserts x is number {
  if (typeof x !== "number") {
    throw new Error(label);
  }
}

function useAssertSecond(x: string | number): number {
  assertSecond("tag", x);
  return x;
}

// Via `never`-returning helper and via nested assertion call.
function fail(msg: string): never {
  throw new Error(msg);
}

function assertViaNever(x: unknown): asserts x is string {
  if (typeof x !== "string") {
    fail("not string");
  }
}

function assertViaNested(x: unknown): asserts x is string {
  assertStr(x);
}

// Inner closure with its own `return` must not trigger the outer assertion check.
function assertWithInnerClosure(x: unknown): asserts x is string {
  const helper = (): number => {
    return 42;
  };
  void helper;
  if (typeof x !== "string") {
    throw new Error("not string");
  }
}

// `try/finally` where `try` returns only when proven and `finally` does not
// return or mutate fields.
function assertTryFinallySafe(x: unknown): asserts x is string {
  try {
    if (typeof x === "string") {
      return;
    }
    throw new Error("not string");
  } finally {
    // cleanup only
  }
}

// Switch-based narrowing.
function assertSwitch(x: "a" | "b" | "c"): asserts x is "a" | "b" {
  switch (x) {
    case "a":
    case "b":
      return;
    default:
      throw new Error("unexpected");
  }
}

// Infinite loop whose only normal exit proves the assertion.
function assertWhileTrue(x: unknown): asserts x is string {
  while (true) {
    if (typeof x === "string") {
      return;
    }
  }
}

// --- 2. Class methods (`asserts x is T`, `asserts this is T`) & explicit `this` ---

interface ReadyBox {
  readonly value: string;
}

class Box {
  readonly value: string | null;
  constructor(v: string | null) {
    this.value = v;
  }
  assertReady(): asserts this is ReadyBox {
    if (this.value === null) {
      throw new Error("not ready");
    }
  }
  checkNum(x: unknown): asserts x is number {
    if (typeof x !== "number") {
      throw new Error("not number");
    }
  }
}

function useBox(b: Box): string {
  b.assertReady();
  return b.value;
}

class BaseAnimal {
  readonly kind: string = "animal";
  assertIsDog(): asserts this is DogAnimal {
    if (!(this instanceof DogAnimal)) {
      throw new Error("not dog");
    }
  }
}

class DogAnimal extends BaseAnimal {
  readonly bark: string = "woof";
}

function useDog(a: BaseAnimal): string {
  a.assertIsDog();
  return a.bark;
}

// Explicit `this` parameter on free function.
function assertThisReady(this: {
  readonly value: string | null;
}): asserts this is ReadyBox {
  if (this.value === null) {
    throw new Error("not ready");
  }
}

// --- 3. Overloaded bodied assertion function (including renamed param) ---

function assertOverload(val: unknown, kind: "str"): asserts val is string;
function assertOverload(val: unknown, kind: "num"): asserts val is number;
function assertOverload(x: unknown, kind: "str" | "num"): void {
  if (kind === "str") {
    if (typeof x !== "string") {
      throw new Error("not str");
    }
  } else {
    if (typeof x !== "number") {
      throw new Error("not num");
    }
  }
}

function useAssertOverload(x: string | number | boolean): number {
  assertOverload(x, "num" as const);
  return x;
}

// --- 4. Soundness rejections (programs tsc accepts, SKJS must reject) ---

// Empty / lying body for `asserts x is T`.
// @skjs-expect-error Assertion body does not establish that 'x' has type 'string'
function badEmptyIs(x: unknown): asserts x is string {}

// Empty / lying body for `asserts x`.
// @skjs-expect-error Assertion body does not establish that 'x' is truthy (its type here is 'boolean')
function badEmptyTruthy(x: boolean): asserts x {}

// Partial falsy elimination (`NaN` is still falsy in `number`).
// @skjs-expect-error Assertion body does not establish that 'x' is truthy (its type here is 'number')
function badPartialTruthyNum(x: number): asserts x {
  if (x === 0) {
    throw new Error("zero");
  }
}

// Missing throw on one branch (fallthrough leaves `x: unknown`).
// @skjs-expect-error Assertion body does not establish that 'x' has type 'string'
function badMissingBranch(cond: boolean, x: unknown): asserts x is string {
  if (cond) {
    if (typeof x !== "string") {
      throw new Error("not string");
    }
  }
}

// Early `return;` before proving the assertion.
function badEarlyReturn(x: unknown): asserts x is string {
  if (typeof x !== "string") {
    // @skjs-expect-error Assertion body does not establish that 'x' has type 'string'
    return;
  }
}

// Reassigning the asserted parameter does NOT mutate the caller's variable.
function badReassignParam(x: unknown): asserts x is string {
  // @skjs-expect-error Cannot assign to 'x' because it is a constant
  x = "ok";
  if (typeof x !== "string") {
    throw new Error("unreachable");
  }
}

// Reassigning the asserted parameter inside a nested closure is also rejected.
function badReassignInClosure(x: unknown): asserts x is string {
  const f = (): void => {
    // @skjs-expect-error Cannot assign to 'x' because it is a constant
    x = "ok";
  };
  f();
  if (typeof x !== "string") {
    throw new Error("not string");
  }
}

// Parameter default replaces `undefined` only locally, not in the caller.
// @skjs-expect-error An asserted parameter cannot have a default value
function badDefaultParam(x: string | undefined = "hi"): asserts x is string {
  if (typeof x !== "string") {
    throw new Error("unreachable");
  }
}

// Shadowing `x` in an inner block does not narrow the outer asserted parameter.
function badShadowBlock(x: unknown): asserts x is string {
  {
    const x: string = "hi";
    void x;
    // @skjs-expect-error Assertion body does not establish that 'x' has type 'string'
    return;
  }
}

// `try/finally` where `finally` swallows the throw via `return;`.
function badFinallySwallow(x: unknown): asserts x is string {
  try {
    if (typeof x !== "string") {
      throw new Error("not string");
    }
  } finally {
    // @skjs-expect-error Assertion body does not establish that 'x' has type 'string'
    return;
  }
}

// `try/finally` where `finally` mutates a field on `this` after `try` returns.
class BadFinallyMutBox {
  value: string | null = null;
  badFinallyMutate(): asserts this is ReadyBox {
    try {
      if (this.value !== null) {
        // @skjs-expect-error Assertion body does not establish that 'this' has type 'ReadyBox'
        return;
      }
      throw new Error("null");
    } finally {
      this.value = null;
    }
  }
}

// Side-effecting call invalidates transient mutable-field narrowing before exit.
declare function sideEffect(): void;
class BadCallInvalidatesBox {
  value: string | null = null;
  // @skjs-expect-error Assertion body does not establish that 'this' has type 'ReadyBox'
  badCallInvalidates(): asserts this is ReadyBox {
    if (this.value === null) {
      throw new Error("null");
    }
    sideEffect();
  }
}

// Receiverless `this: void` cannot satisfy `asserts this`.
// @skjs-expect-error Assertion body does not establish the asserted predicate on 'this'
function badReceiverlessThis(this: void): asserts this {}

// Class method `asserts this is T` that does not prove `this` satisfies `T`.
class BadBox {
  readonly value: string | null;
  constructor(v: string | null) {
    this.value = v;
  }
  // @skjs-expect-error Assertion body does not establish that 'this' has type 'ReadyBox'
  badAssertReady(): asserts this is ReadyBox {}
}

// Mutable field refinement is transient: an alias write in the caller after
// returning must invalidate the narrowed field.
interface MutableBox {
  value: string | null;
  assertReady(): asserts this is ReadyBox;
}
function useMutableBoxAliasWrite(b: MutableBox): string {
  const alias: MutableBox = b;
  b.assertReady();
  alias.value = null;
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return b.value;
}

// Lying overload implementation does not prove the overload's assertion.
// @skjs-expect-error Overload signature is not compatible with its implementation signature
function badOverloadAssert(val: unknown, kind: "str"): asserts val is string;
function badOverloadAssert(x: unknown, kind: "str"): void {
  void x;
  void kind;
}

// --- 5. Errors also rejected by tsc ---

// Returning a non-void value in a bodied assertion function.
function badReturnValue(x: unknown): asserts x is string {
  if (typeof x !== "string") {
    throw new Error("not string");
  }
  // @ts-expect-error Type of returned value is not assignable to the function's return type
  return 1;
}

// Async assertion function (return type is void, not Promise<T>).
// @ts-expect-error The return type of an async function must be the global Promise<T> type
// @skjs-expect-error Not all code paths return a value, and the return type does not include 'undefined'
async function badAsyncAssert(x: unknown): asserts x is string {
  if (typeof x !== "string") {
    throw new Error("not string");
  }
}
