// Assertion signatures (`asserts x` and `asserts x is T`) — issue #583.
//
// Declared/ambient assertion signatures narrow the asserted local variable for
// the remainder of the enclosing scope after a top-level expression statement
// call returns normally.

// 1. Basic declared assertion functions (`asserts x` and `asserts x is T`).
declare function assertTruthy(x: unknown): asserts x;
declare function assertString(x: unknown): asserts x is string;
declare function assertDefined<T>(x: T | null | undefined): asserts x is T;

function useAssertString(x: string | number): string {
  assertString(x);
  return x;
}

function useAssertTruthy(x: string | null | undefined): string {
  assertTruthy(x);
  return x;
}

function useAssertTruthyBool(x: boolean): true {
  assertTruthy(x);
  return x;
}

function useAssertDefined(x: number | null | undefined): number {
  assertDefined(x);
  return x;
}

// 2. Assertion on a non-first parameter.
declare function assertSecond(label: string, x: unknown): asserts x is number;

function useSecond(x: string | number): number {
  assertSecond("tag", x);
  return x;
}

// 3. Function type annotations with assertion signatures.
type AssertStrFn = (x: unknown) => asserts x is string;
type AssertTruthFn = (x: unknown) => asserts x;

declare const fnAssertStr: AssertStrFn;
declare const fnAssertTruth: AssertTruthFn;

function useFnType(x: string | number): string {
  fnAssertStr(x);
  return x;
}

function useFnTypeTruth(x: string | null): string {
  fnAssertTruth(x);
  return x;
}

// 4. Interface methods with `asserts this` and `asserts this is T`.
interface ReadyBox {
  readonly value: string;
}
interface MaybeBox {
  readonly value: string | null;
  assertReady(): asserts this is ReadyBox;
}

interface SelfAssertBox {
  assertSelf(): asserts this;
}

function useAssertThis(box: MaybeBox): string {
  box.assertReady();
  return box.value;
}

function useAssertSelf(box: SelfAssertBox): void {
  box.assertSelf();
}

// 5. Overloaded assertion signatures.
declare function assertKind(x: unknown, kind: "str"): asserts x is string;
declare function assertKind(x: unknown, kind: "num"): asserts x is number;

function useOverload(x: string | number | boolean): number {
  assertKind(x, "num" as const);
  return x;
}

// 6. Union of assertion functions: only narrows when branches agree.
function useUnionAgree(cond: boolean, x: string | number): string {
  const fn: AssertStrFn | AssertStrFn = cond ? fnAssertStr : fnAssertStr;
  fn(x);
  return x;
}

type AssertNumFn = (x: unknown) => asserts x is number;
declare const fnAssertNum: AssertNumFn;

function useUnionDisagree(cond: boolean, x: string | number): string {
  const fn: AssertStrFn | AssertNumFn = cond ? fnAssertStr : fnAssertNum;
  fn(x);
  // @ts-expect-error Type of returned value is not assignable to the function's return type
  return x;
}

// 7. Soundness: captured mutable `let` must NOT be narrowed by an assertion
// call, because the callee could mutate the outer binding via a closure before
// returning normally (even without calling the callback explicitly at the call
// site, `assertString` itself could invoke a previously registered callback).
declare function registerCallback(cb: () => void): void;
function useCapturedMutableLet(): string {
  let x: string | number = "init";
  registerCallback(() => {
    x = 42;
  });
  assertString(x);
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x;
}

// 8. Non-top-level expression statement: optional chaining (`?.`) can skip the
// call when the receiver is nullish, so it must NOT narrow.
function useOptionalChain(box: MaybeBox | undefined): string {
  box?.assertReady();
  // @ts-expect-error Property access is not allowed on this type
  return box.value;
}

// 9. try/catch: narrowing applies after the assertion inside `try`, while
// `catch` sees the pre-assertion type (the assertion itself may have thrown).
function useTryCatch(x: string | number): string {
  try {
    assertString(x);
    const ok: string = x;
    return ok;
  } catch {
    // @ts-expect-error Type of returned value is not assignable to the function's return type
    return x;
  }
}

// 10. Assertion function subtyping:
// - Dropping an assertion predicate to `(...) => void` is allowed.
// - Assigning a plain `(...) => void` to an assertion signature is rejected
//   (stricter than tsc, which unsoundly accepts it).
// - Assigning a different assertion kind or incompatible target is rejected.
declare function plainVoid(x: unknown): void;
declare function assertLiteralA(x: unknown): asserts x is "a";

function testDropToVoid(): void {
  const okDrop: (x: unknown) => void = assertString;
  void okDrop;
}

function testBadPlainToAssert(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const badPlainToAssert: AssertStrFn = plainVoid;
  void badPlainToAssert;
}

function testBadPlainToTruth(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const badPlainToTruth: AssertTruthFn = plainVoid;
  void badPlainToTruth;
}

function testBadTruthToIs(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const badTruthToIs: AssertStrFn = assertTruthy;
  void badTruthToIs;
}

function testBadIsToTruth(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const badIsToTruth: AssertTruthFn = assertString;
  void badIsToTruth;
}

function testCovariantTarget(): void {
  const okCovariantTarget: AssertStrFn = assertLiteralA;
  void okCovariantTarget;
}

function testBadWiderTarget(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const badWiderTarget: (x: unknown) => asserts x is "a" = assertString;
  void badWiderTarget;
}

// 10b. Standalone `asserts x` on boolean condition expression (`asserts cond`).
declare function assertCondition(cond: boolean): asserts cond;

function useAssertCondition(x: string | number): string {
  assertCondition(typeof x === "string");
  return x;
}

// 11. Bodied assertion functions are accepted when every normal return path
// proves the asserted postcondition (full bodied coverage lives in
// `assertion-functions-bodied.ts`).
function okBodiedAssert(x: unknown): asserts x is string {
  if (typeof x !== "string") {
    throw new Error("not string");
  }
}

function okBodiedTruthy(x: boolean): asserts x {
  if (!x) {
    throw new Error("falsy");
  }
}

class OkClassAssert {
  check(x: unknown): asserts x is string {
    if (typeof x !== "string") {
      throw new Error("not string");
    }
  }
}

// 12. Validation errors: unknown parameter, rest parameter, nested position,
// and construct signature.
// @ts-expect-error Cannot find parameter 'y'
declare function badUnknownParam(x: unknown): asserts y is string;
// @ts-expect-error Cannot find parameter 'y'
declare function badUnknownParamTruthy(x: unknown): asserts y;
// @ts-expect-error A type predicate cannot reference a rest parameter
declare function badRest(...xs: readonly unknown[]): asserts xs is string[];
// @ts-expect-error A type predicate is only allowed in return type position for functions and methods
declare function badNested(x: unknown): Promise<asserts x is string>;
// @ts-expect-error A type predicate is only allowed in return type position for functions and methods
type BadConstruct = new (x: unknown) => asserts x is string;
// @ts-expect-error Cannot find type 'NonExistentAssertType'
declare function badTargetType(x: unknown): asserts x is NonExistentAssertType;
