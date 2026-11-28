// Bodied type predicate functions and methods (`x is T`, `this is T`) —
// SkipLabs/skjs#582.
//
// Soundness verification: every reachable `return expr;` in a bodied type
// predicate must prove BOTH:
//   1. True branch (`expr === true`): the subject is narrowed to a subtype of
//      the claimed target type.
//   2. False branch (`expr === false`): no runtime value of the subject
//      inhabiting the target type can reach the return and evaluate `expr` to
//      `false` (required because call-site `else` branches subtract the target
//      type).

// --- 1. Valid bodied `x is T` functions ---

// 1a. `typeof` checks and nullish checks
function isStr(x: unknown): x is string {
  return typeof x === "string";
}

function isNum(x: unknown): x is number {
  return typeof x === "number";
}

function isBool(x: unknown): x is boolean {
  return typeof x === "boolean";
}

function isUndef(x: string | undefined): x is undefined {
  return x === undefined;
}

function isNotNull(x: string | null): x is string {
  return x !== null;
}

function isNullOrUndef(x: string | null | undefined): x is null | undefined {
  return x === null || x === undefined;
}

// Generic `isDefined`: requires a non-nullish constraint (e.g. `T extends object`)
// so `null`/`undefined` cannot instantiate `T`; see negative test 3f for the
// unconstrained `<T>` soundness trap!
function isDefinedObj<T extends object>(x: T | null | undefined): x is T {
  return x !== null && x !== undefined;
}

// 1b. Literal equality
function isLitA(x: "a" | "b"): x is "a" {
  return x === "a";
}

function isTrueLit(x: boolean): x is true {
  return x === true;
}

// 1c. Negated predicate / compound logical expressions
function isNotStr(x: string | number): x is number {
  return typeof x !== "string";
}

function isStrOrNum(x: unknown): x is string | number {
  return typeof x === "string" || typeof x === "number";
}

// 1d. Composing existing type predicates
function isStrViaHelper(x: unknown): x is string {
  return isStr(x);
}

function isStrOrNumViaHelpers(x: unknown): x is string | number {
  return isStr(x) || isNum(x);
}

// 1e. Branch-narrowed `return true` / `return false`
function isStrBranched(x: unknown): x is string {
  if (typeof x === "string") {
    return true;
  }
  return false;
}

function isStrEarlyFalse(x: unknown): x is string {
  if (typeof x !== "string") {
    return false;
  }
  return true;
}

// 1f. Discriminated union via field equality
interface Circle {
  readonly kind: "circle";
  readonly radius: number;
}
interface Square {
  readonly kind: "square";
  readonly side: number;
}
type Shape = Circle | Square;

function isCircle(s: Shape): s is Circle {
  return s.kind === "circle";
}

// 1g. `Array.isArray`
function isStrArray(x: string[] | number): x is string[] {
  return Array.isArray(x);
}

// 1h. `instanceof` on a nominal class without custom `[Symbol.hasInstance]`
class Cat {
  readonly meow: number = 1;
}
class Dog {
  readonly bark: number = 2;
}

function isCat(x: Cat | Dog): x is Cat {
  return x instanceof Cat;
}

// 1i. Non-first parameter subject
function isSecondStr(tag: number, x: unknown): x is string {
  void tag;
  return typeof x === "string";
}

// 1j. Nested closure inside a bodied predicate must not inherit active predicate
function isStrWithInnerLambda(x: unknown): x is string {
  const helper = (): boolean => {
    return true;
  };
  void helper;
  return typeof x === "string";
}

// 1k. Call-site narrowing works with bodied predicates (true + false branches)
export function useBodiedIsStr(x: string | number): number {
  if (isStr(x)) {
    return x.length;
  }
  return x + 1;
}

export function useBodiedIsCircle(s: Shape): number {
  if (isCircle(s)) {
    return s.radius;
  }
  return s.side;
}

export function useBodiedIsDefinedObj(x: Circle | null | undefined): number {
  if (isDefinedObj<Circle>(x)) {
    return x.radius;
  }
  return 0;
}

// 1l. `this is Sub` method on a nominal class hierarchy
class BaseNode {
  readonly kind: string = "base";
  isLeaf(): this is LeafNode {
    return this instanceof LeafNode;
  }
}
class LeafNode extends BaseNode {
  readonly value: number = 0;
}

export function useBodiedThisPred(n: BaseNode): number {
  if (n.isLeaf()) {
    return n.value;
  }
  return n.kind.length;
}

// 1m. Overloaded bodied type predicate
function isTagged(x: unknown, tag: "s"): x is string;
function isTagged(x: unknown, tag: "n"): x is number;
function isTagged(x: unknown, tag: "s" | "n"): boolean {
  if (tag === "s") {
    return typeof x === "string";
  }
  return typeof x === "number";
}

export function useOverloadedBodiedPred(x: string | number): number {
  if (isTagged(x, "s")) {
    return x.length;
  }
  return x + 1;
}

// --- 2. Unsound / invalid bodied type predicates (true-branch failures) ---

// 2a. Lying body: returns `true` unconditionally
function badAlwaysTrue(x: unknown): x is string {
  // @skjs-expect-error Cannot prove 'x' is 'string' when returning 'true': 'x' has type 'unknown'
  return true;
}

// 2b. Wrong type check: `typeof x === "number"` claimed as `x is string`
function badWrongType(x: unknown): x is string {
  // @skjs-expect-error Cannot prove 'x' is 'string' when returning 'true': 'x' has type 'number'
  return typeof x === "number";
}

// 2c. Opaque boolean expression
function badOpaqueBool(x: unknown, flag: boolean): x is string {
  void x;
  // @skjs-expect-error Cannot prove 'x' is 'string' when returning 'true': 'x' has type 'unknown'
  return flag;
}

// 2d. `||` widens true branch beyond target
function badOrTooWide(x: unknown): x is string {
  // @skjs-expect-error Cannot prove 'x' is 'string' when returning 'true': 'x' has type 'number | string'
  return typeof x === "string" || typeof x === "number";
}

// 2e. One branch returns `true` without narrowing
function badUnprovenBranch(x: unknown, flag: boolean): x is string {
  if (flag) {
    // @skjs-expect-error Cannot prove 'x' is 'string' when returning 'true': 'x' has type 'unknown'
    return true;
  }
  return typeof x === "string";
}

// --- 3. Unsound false-branch subtraction traps (CRITICAL SOUNDNESS) ---

// 3a. Narrower condition than claimed target: `isPositive(-1)` returns `false`,
// which would unsoundly exclude `number` from `number | string` in an `else`!
function badPositiveNumber(x: number | string): x is number {
  // @skjs-expect-error Cannot prove 'x' is not 'number' when returning 'false': a value of type 'number' may still reach this return
  return typeof x === "number" && x > 0;
}

// 3b. Returning `false` unconditionally when subject could still be `target`
function badAlwaysFalse(x: string | number): x is string {
  void x;
  // @skjs-expect-error Cannot prove 'x' is not 'string' when returning 'false': a value of type 'string' may still reach this return
  return false;
}

// 3c. Narrower target tested: `x === "a"` claimed as `x is string`
function badSubsetOfTarget(x: string | number): x is string {
  // @skjs-expect-error Cannot prove 'x' is not 'string' when returning 'false': a value of type 'string' may still reach this return
  return x === "a";
}

// 3d. Early `return false` when subject could still be `target`
function badEarlyFalseWhenTarget(
  x: string | number,
  flag: boolean,
): x is string {
  if (flag) {
    // @skjs-expect-error Cannot prove 'x' is not 'string' when returning 'false': a value of type 'string' may still reach this return
    return false;
  }
  return typeof x === "string";
}

// 3e. `x instanceof CustomHasInstance` cannot narrow (custom Symbol.hasInstance)
class CustomHasInstance {
  readonly a: number = 1;
  static [Symbol.hasInstance](_x: unknown): boolean {
    return true;
  }
}

function badCustomHasInstance(x: unknown): x is CustomHasInstance {
  // @skjs-expect-error Cannot prove 'x' is 'CustomHasInstance' when returning 'true': 'x' has type 'unknown'
  return x instanceof CustomHasInstance;
}

// 3f. Unconstrained `<T>` can be instantiated with `null` or `undefined`:
// `badUnconstrainedDefined<null>(null)` returns `false` and `else` would
// unsoundly subtract `null` from `null` to `never`.
function badUnconstrainedDefined<T>(x: T | null | undefined): x is T {
  // @skjs-expect-error Cannot prove 'x' is not 'T' when returning 'false': a value of type 'T' may still reach this return
  return x !== null && x !== undefined;
}

// --- 4. Parameter reassignment, defaults, shadowing, try/finally, mutable fields ---

// 4a. Reassigning the predicate parameter does not change the caller's variable
function badReassignParam(x: unknown): x is string {
  // @skjs-expect-error Cannot assign to 'x' because it is a constant
  x = "ok";
  return typeof x === "string";
}

// 4b. Predicate parameter with a default value (default substitutes locally, not at caller)
// @skjs-expect-error A type predicate parameter cannot have a default initializer
function badDefaultParam(x: string | undefined = "ok"): x is string {
  return typeof x === "string";
}

// 4c. Shadowing the parameter in an inner block must not spoof the predicate
function badShadowBlock(x: unknown): x is string {
  void x;
  {
    const x: string = "ok";
    // @skjs-expect-error Cannot prove 'x' is 'string' when returning 'true': 'x' has type 'unknown'
    return typeof x === "string";
  }
}

// 4d. Side-effecting `finally` mutating a mutable field on `this` after `try` returns
interface ReadyBox {
  readonly value: string;
}
class BadFinallyMutBox {
  value: string | null = null;
  isReady(): this is ReadyBox {
    try {
      // @skjs-expect-error Cannot prove 'this' is 'ReadyBox' when returning 'true': 'this' has type 'this extends BadFinallyMutBox'
      return this.value !== null;
    } finally {
      this.value = null;
    }
  }
}

// 4e. Side-effecting call invalidates transient mutable-field narrowing before return
declare function sideEffect(): void;
class BadCallInvalidatesBox {
  value: string | null = null;
  isReady(): this is ReadyBox {
    if (this.value !== null) {
      sideEffect();
      // @skjs-expect-error Cannot prove 'this' is 'ReadyBox' when returning 'true': 'this' has type 'this extends BadCallInvalidatesBox'
      return true;
    }
    return false;
  }
}

// 4f. Caller alias write after `this is ReadyBox` must invalidate mutable field
class MutableBox {
  value: string | null = null;
  isReady(): this is ReadyBox {
    return this.value !== null;
  }
}

export function useMutableBoxAliasWrite(b: MutableBox): string {
  const alias: MutableBox = b;
  if (b.isReady()) {
    alias.value = null;
    // @skjs-expect-error Type of returned value is not assignable to the function's return type
    return b.value;
  }
  return "";
}

// 4g. Receiverless `this: void` cannot satisfy `this is T`
function badReceiverlessThis(this: void): this is ReadyBox {
  // @skjs-expect-error Cannot prove type predicate on 'this' for type 'ReadyBox' because 'this' is not in scope
  return false;
}

// 4h. Async function cannot have a type predicate return type
// @ts-expect-error The return type of an async function must be the global Promise<T> type
async function badAsyncPred(x: unknown): x is string {
  return typeof x === "string";
}

// 4i. Returning non-boolean value in bodied predicate
function badReturnNonBool(x: unknown): x is string {
  void x;
  // @ts-expect-error Type of returned value is not assignable to the function's return type
  return 42;
}
