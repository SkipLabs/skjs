// Bodied assertion functions (`asserts x`, `asserts x is T`, `asserts this`,
// `asserts this is T`) — issue #583.
//
// Pinning test: currently all bodied assertion functions are rejected with
// SKJS9013 (soundness: body not yet verified).

// --- 1. Valid bodied `asserts x is T` and `asserts x` functions ---

// @skjs-expect-error An assertion signature ('asserts') is only supported on declared function, method, or function-type signatures
function assertStr(x: unknown): asserts x is string {
  if (typeof x !== "string") {
    throw new Error("not string");
  }
}

function useAssertStr(x: string | number): string {
  assertStr(x);
  return x;
}

// @skjs-expect-error An assertion signature ('asserts') is only supported on declared function, method, or function-type signatures
function assertTruthyBool(x: boolean): asserts x {
  if (!x) {
    throw new Error("falsy");
  }
}

function useAssertTruthyBool(x: string | number): string {
  assertTruthyBool(typeof x === "string");
  return x;
}

// @skjs-expect-error An assertion signature ('asserts') is only supported on declared function, method, or function-type signatures
function assertTruthyObj(x: { readonly a: number } | null): asserts x {
  if (!x) {
    throw new Error("null");
  }
}

function useAssertTruthyObj(x: { readonly a: number } | null): number {
  assertTruthyObj(x);
  return x.a;
}

// @skjs-expect-error An assertion signature ('asserts') is only supported on declared function, method, or function-type signatures
function assertTruthyZeroOrOne(x: 0 | 1): asserts x {
  if (x === 0) {
    throw new Error("zero");
  }
}

function useAssertTruthyZeroOrOne(x: 0 | 1): 1 {
  assertTruthyZeroOrOne(x);
  return x;
}

// @skjs-expect-error An assertion signature ('asserts') is only supported on declared function, method, or function-type signatures
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
// @skjs-expect-error An assertion signature ('asserts') is only supported on declared function, method, or function-type signatures
function assertEarlyReturn(x: unknown): asserts x is string {
  if (typeof x === "string") {
    return;
  }
  throw new Error("not string");
}

// @skjs-expect-error An assertion signature ('asserts') is only supported on declared function, method, or function-type signatures
function assertReturnUndefined(x: unknown): asserts x is string {
  if (typeof x === "string") {
    return undefined;
  }
  throw new Error("not string");
}

// Non-first parameter.
// @skjs-expect-error An assertion signature ('asserts') is only supported on declared function, method, or function-type signatures
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

// @skjs-expect-error An assertion signature ('asserts') is only supported on declared function, method, or function-type signatures
function assertViaNever(x: unknown): asserts x is string {
  if (typeof x !== "string") {
    fail("not string");
  }
}

// @skjs-expect-error An assertion signature ('asserts') is only supported on declared function, method, or function-type signatures
function assertViaNested(x: unknown): asserts x is string {
  assertStr(x);
}

// Inner closure with its own `return` must not trigger the outer assertion check.
// @skjs-expect-error An assertion signature ('asserts') is only supported on declared function, method, or function-type signatures
function assertWithInnerClosure(x: unknown): asserts x is string {
  const helper = (): number => {
    return 42;
  };
  void helper;
  if (typeof x !== "string") {
    throw new Error("not string");
  }
}

// `try/finally` where `try` returns only when proven and `finally` does not return.
// @skjs-expect-error An assertion signature ('asserts') is only supported on declared function, method, or function-type signatures
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
// @skjs-expect-error An assertion signature ('asserts') is only supported on declared function, method, or function-type signatures
function assertSwitch(x: "a" | "b" | "c"): asserts x is "a" | "b" {
  switch (x) {
    case "a":
    case "b":
      return;
    default:
      throw new Error("unexpected");
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
  // @skjs-expect-error An assertion signature ('asserts') is only supported on declared function, method, or function-type signatures
  assertReady(): asserts this is ReadyBox {
    if (this.value === null) {
      throw new Error("not ready");
    }
  }
  // @skjs-expect-error An assertion signature ('asserts') is only supported on declared function, method, or function-type signatures
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
  // @skjs-expect-error An assertion signature ('asserts') is only supported on declared function, method, or function-type signatures
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
function assertThisReady(
  this: { readonly value: string | null },
  // @skjs-expect-error An assertion signature ('asserts') is only supported on declared function, method, or function-type signatures
): asserts this is ReadyBox {
  if (this.value === null) {
    throw new Error("not ready");
  }
}

// --- 3. Overloaded bodied assertion function (including renamed param) ---

// @skjs-expect-error Overload signature is not compatible with its implementation signature
function assertOverload(val: unknown, kind: "str"): asserts val is string;
// @skjs-expect-error Overload signature is not compatible with its implementation signature
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
// @skjs-expect-error An assertion signature ('asserts') is only supported on declared function, method, or function-type signatures
function badEmptyIs(x: unknown): asserts x is string {}

// Empty / lying body for `asserts x`.
// @skjs-expect-error An assertion signature ('asserts') is only supported on declared function, method, or function-type signatures
function badEmptyTruthy(x: boolean): asserts x {}

// Partial falsy elimination (`NaN` is still falsy in `number`).
// @skjs-expect-error An assertion signature ('asserts') is only supported on declared function, method, or function-type signatures
function badPartialTruthyNum(x: number): asserts x {
  if (x === 0) {
    throw new Error("zero");
  }
}

// Missing throw on one branch (fallthrough leaves `x: unknown`).
// @skjs-expect-error An assertion signature ('asserts') is only supported on declared function, method, or function-type signatures
function badMissingBranch(cond: boolean, x: unknown): asserts x is string {
  if (cond) {
    if (typeof x !== "string") {
      throw new Error("not string");
    }
  }
}

// Early `return;` before proving the assertion.
// @skjs-expect-error An assertion signature ('asserts') is only supported on declared function, method, or function-type signatures
function badEarlyReturn(x: unknown): asserts x is string {
  if (typeof x !== "string") {
    return;
  }
}

// Reassigning the asserted parameter does NOT mutate the caller's variable.
// @skjs-expect-error An assertion signature ('asserts') is only supported on declared function, method, or function-type signatures
function badReassignParam(x: unknown): asserts x is string {
  x = "ok";
  if (typeof x !== "string") {
    throw new Error("unreachable");
  }
}

// Parameter default replaces `undefined` only locally, not in the caller.
// @skjs-expect-error An assertion signature ('asserts') is only supported on declared function, method, or function-type signatures
function badDefaultParam(x: string | undefined = "hi"): asserts x is string {
  if (typeof x !== "string") {
    throw new Error("unreachable");
  }
}

// Shadowing `x` in an inner block does not narrow the outer asserted parameter.
// @skjs-expect-error An assertion signature ('asserts') is only supported on declared function, method, or function-type signatures
function badShadowBlock(x: unknown): asserts x is string {
  {
    const x: string = "hi";
    void x;
    return;
  }
}

// `try/finally` where `finally` swallows the throw via `return;`.
// @skjs-expect-error An assertion signature ('asserts') is only supported on declared function, method, or function-type signatures
function badFinallySwallow(x: unknown): asserts x is string {
  try {
    if (typeof x !== "string") {
      throw new Error("not string");
    }
  } finally {
    return;
  }
}

// Class method `asserts this is T` that does not prove `this` satisfies `T`.
class BadBox {
  readonly value: string | null;
  constructor(v: string | null) {
    this.value = v;
  }
  // @skjs-expect-error An assertion signature ('asserts') is only supported on declared function, method, or function-type signatures
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
  // Currently unsoundly accepted (evalAssertIs does not mark field refinement).
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
// @skjs-expect-error An assertion signature ('asserts') is only supported on declared function, method, or function-type signatures
function badReturnValue(x: unknown): asserts x is string {
  if (typeof x !== "string") {
    throw new Error("not string");
  }
  // @ts-expect-error Type of returned value is not assignable to the function's return type
  return 1;
}

// Async assertion function (return type is void, not Promise<T>).
// @skjs-expect-error An assertion signature ('asserts') is only supported on declared function, method, or function-type signatures
// @ts-expect-error The return type of an async function must be the global Promise<T> type
// @skjs-expect-error Not all code paths return a value, and the return type does not include 'undefined'
async function badAsyncAssert(x: unknown): asserts x is string {
  if (typeof x !== "string") {
    throw new Error("not string");
  }
}
