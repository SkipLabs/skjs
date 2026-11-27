// Assertion signatures (`asserts x` and `asserts x is T`) — pinning tests for
// issue #583.
//
// Declared/ambient assertion signatures are currently rejected with SKJS9013;
// these tests pin the current behavior before assertion signatures are
// implemented.

// 1. Basic declared assertion functions (`asserts x` and `asserts x is T`).
// @skjs-expect-error 'asserts' type predicates are not yet supported by SKJS
declare function assertTruthy(x: unknown): asserts x;
// @skjs-expect-error 'asserts' type predicates are not yet supported by SKJS
declare function assertString(x: unknown): asserts x is string;
// @skjs-expect-error 'asserts' type predicates are not yet supported by SKJS
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

// 2. Assertion on an optional parameter or a second parameter.
// @skjs-expect-error 'asserts' type predicates are not yet supported by SKJS
declare function assertSecond(label: string, x: unknown): asserts x is number;

function useSecond(x: string | number): number {
  assertSecond("tag", x);
  return x;
}

// 3. Function type annotations with assertion signatures.
// @skjs-expect-error 'asserts' type predicates are not yet supported by SKJS
type AssertStrFn = (x: unknown) => asserts x is string;
// @skjs-expect-error 'asserts' type predicates are not yet supported by SKJS
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

// 4. Interface and class methods with `asserts this` and `asserts this is T`.
interface ReadyBox {
  readonly value: string;
}
interface MaybeBox {
  readonly value: string | null;
  // @skjs-expect-error 'asserts' type predicates are not yet supported by SKJS
  assertReady(): asserts this is ReadyBox;
}

interface SelfAssertBox {
  // @skjs-expect-error 'asserts' type predicates are not yet supported by SKJS
  assertSelf(): asserts this;
}

function useAssertThis(box: MaybeBox): string {
  box.assertReady();
  return box.value;
}

function useAssertSelf(box: SelfAssertBox): void {
  box.assertSelf();
}

// 5. Generic and overloaded assertion signatures.
// @skjs-expect-error 'asserts' type predicates are not yet supported by SKJS
declare function assertKind(x: unknown, kind: "str"): asserts x is string;
// @skjs-expect-error 'asserts' type predicates are not yet supported by SKJS
declare function assertKind(x: unknown, kind: "num"): asserts x is number;

function useOverload(x: string | number | boolean): number {
  assertKind(x, "num");
  return x;
}

// 6. Union of assertion functions: only narrows when branches agree.
function useUnionAgree(cond: boolean, x: string | number): string {
  const fn: AssertStrFn | AssertStrFn = cond ? fnAssertStr : fnAssertStr;
  fn(x);
  return x;
}

// @skjs-expect-error 'asserts' type predicates are not yet supported by SKJS
type AssertNumFn = (x: unknown) => asserts x is number;
declare const fnAssertNum: AssertNumFn;

function useUnionDisagree(cond: boolean, x: string | number): string {
  const fn: AssertStrFn | AssertNumFn = cond ? fnAssertStr : fnAssertNum;
  fn(x);
  return x;
}

// 7. Soundness: captured mutable `let` must NOT be narrowed by an assertion
// call, because the callee could mutate the outer binding via a closure before
// returning normally (even without calling `mutate()` explicitly at the call
// site, `assertString` itself could invoke a previously registered callback).
declare function registerCallback(cb: () => void): void;
function useCapturedMutableLet(): string {
  let x: string | number = "init";
  registerCallback(() => {
    x = 42;
  });
  assertString(x);
  return x;
}

// 8. Non-top-level expression statement: optional chaining (`?.`) or value-used
// calls must NOT narrow the surrounding scope.
function useOptionalChain(box: MaybeBox | undefined): string {
  box?.assertReady();
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
    return x;
  }
}

// 10. Assertion function subtyping:
// - Dropping an assertion predicate to `(...) => void` is allowed.
// - Assigning a plain `(...) => void` to an assertion signature is rejected.
// - Assigning a different assertion kind or incompatible target is rejected.
declare function plainVoid(x: unknown): void;
// @skjs-expect-error 'asserts' type predicates are not yet supported by SKJS
declare function assertLiteralA(x: unknown): asserts x is "a";

function testDropToVoid(): void {
  const okDrop: (x: unknown) => void = assertString;
  void okDrop;
}

function testBadPlainToAssert(): void {
  const badPlainToAssert: AssertStrFn = plainVoid;
  void badPlainToAssert;
}

function testBadPlainToTruth(): void {
  const badPlainToTruth: AssertTruthFn = plainVoid;
  void badPlainToTruth;
}

function testBadTruthToIs(): void {
  const badTruthToIs: AssertStrFn = assertTruthy;
  void badTruthToIs;
}

function testBadIsToTruth(): void {
  const badIsToTruth: AssertTruthFn = assertString;
  void badIsToTruth;
}

function testCovariantTarget(): void {
  const okCovariantTarget: AssertStrFn = assertLiteralA;
  void okCovariantTarget;
}

function testBadWiderTarget(): void {
  const badWiderTarget: (x: unknown) => asserts x is "a" = assertString;
  void badWiderTarget;
}

// 10b. Standalone `asserts x` on boolean condition expression (`asserts cond`).
// @skjs-expect-error 'asserts' type predicates are not yet supported by SKJS
declare function assertCondition(cond: boolean): asserts cond;

function useAssertCondition(x: string | number): string {
  assertCondition(typeof x === "string");
  return x;
}

// 11. Assertion functions on bodied implementations remain rejected (soundness:
// SKJS does not verify the body against the claimed assertion).
// @skjs-expect-error 'asserts' type predicates are not yet supported by SKJS
function badBodiedAssert(x: unknown): asserts x is string {
  if (typeof x !== "string") {
    throw new Error("not string");
  }
}

// @skjs-expect-error 'asserts' type predicates are not yet supported by SKJS
function badBodiedTruthy(x: unknown): asserts x {
  if (!x) {
    throw new Error("falsy");
  }
}

class BadClassAssert {
  // @skjs-expect-error 'asserts' type predicates are not yet supported by SKJS
  check(x: unknown): asserts x is string {
    if (typeof x !== "string") {
      throw new Error("not string");
    }
  }
}

// 12. Validation errors: unknown parameter, rest parameter, nested position,
// and construct signature.
// @skjs-expect-error 'asserts' type predicates are not yet supported by SKJS
declare function badUnknownParam(x: unknown): asserts y is string;
// @skjs-expect-error 'asserts' type predicates are not yet supported by SKJS
declare function badUnknownParamTruthy(x: unknown): asserts y;
// @skjs-expect-error 'asserts' type predicates are not yet supported by SKJS
declare function badRest(...xs: readonly unknown[]): asserts xs is string[];
// @skjs-expect-error 'asserts' type predicates are not yet supported by SKJS
declare function badNested(x: unknown): Promise<asserts x is string>;
// @skjs-expect-error 'asserts' type predicates are not yet supported by SKJS
type BadConstruct = new (x: unknown) => asserts x is string;
// @skjs-expect-error 'asserts' type predicates are not yet supported by SKJS
declare function badTargetType(x: unknown): asserts x is NonExistentAssertType;
