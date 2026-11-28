// Bodied type predicate functions and methods (`x is T`, `this is T`) —
// SkipLabs/skjs#582.
//
// Pinning test: currently all bodied type predicates are rejected with
// SKJS9032 (soundness: body not yet verified).

// --- 1. Valid bodied `x is T` functions ---

// 1a. `typeof` checks
// @skjs-expect-error A type predicate ('x is T') is only supported as the top-level return type of a declared function or method signature
function isStr(x: unknown): x is string {
  return typeof x === "string";
}

// @skjs-expect-error A type predicate ('x is T') is only supported as the top-level return type of a declared function or method signature
function isNum(x: unknown): x is number {
  return typeof x === "number";
}

// @skjs-expect-error A type predicate ('x is T') is only supported as the top-level return type of a declared function or method signature
function isBool(x: unknown): x is boolean {
  return typeof x === "boolean";
}

// @skjs-expect-error A type predicate ('x is T') is only supported as the top-level return type of a declared function or method signature
function isUndef(x: string | undefined): x is undefined {
  return x === undefined;
}

// @skjs-expect-error A type predicate ('x is T') is only supported as the top-level return type of a declared function or method signature
function isNotNull(x: string | null): x is string {
  return x !== null;
}

// @skjs-expect-error A type predicate ('x is T') is only supported as the top-level return type of a declared function or method signature
function isNullOrUndef(x: string | null | undefined): x is null | undefined {
  return x === null || x === undefined;
}

// @skjs-expect-error A type predicate ('x is T') is only supported as the top-level return type of a declared function or method signature
function isDefined<T>(x: T | null | undefined): x is T {
  return x !== null && x !== undefined;
}

// 1b. Literal equality
// @skjs-expect-error A type predicate ('x is T') is only supported as the top-level return type of a declared function or method signature
function isLitA(x: "a" | "b"): x is "a" {
  return x === "a";
}

// @skjs-expect-error A type predicate ('x is T') is only supported as the top-level return type of a declared function or method signature
function isTrueLit(x: boolean): x is true {
  return x === true;
}

// 1c. Negated predicate / compound logical expressions
// @skjs-expect-error A type predicate ('x is T') is only supported as the top-level return type of a declared function or method signature
function isNotStr(x: string | number): x is number {
  return typeof x !== "string";
}

// @skjs-expect-error A type predicate ('x is T') is only supported as the top-level return type of a declared function or method signature
function isStrOrNum(x: unknown): x is string | number {
  return typeof x === "string" || typeof x === "number";
}

// 1d. Composing existing type predicates
// @skjs-expect-error A type predicate ('x is T') is only supported as the top-level return type of a declared function or method signature
function isStrViaHelper(x: unknown): x is string {
  return isStr(x);
}

// @skjs-expect-error A type predicate ('x is T') is only supported as the top-level return type of a declared function or method signature
function isStrOrNumViaHelpers(x: unknown): x is string | number {
  return isStr(x) || isNum(x);
}

// 1e. Branch-narrowed `return true` / `return false`
// @skjs-expect-error A type predicate ('x is T') is only supported as the top-level return type of a declared function or method signature
function isStrBranched(x: unknown): x is string {
  if (typeof x === "string") {
    return true;
  }
  return false;
}

// @skjs-expect-error A type predicate ('x is T') is only supported as the top-level return type of a declared function or method signature
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

// @skjs-expect-error A type predicate ('x is T') is only supported as the top-level return type of a declared function or method signature
function isCircle(s: Shape): s is Circle {
  return s.kind === "circle";
}

// 1g. `Array.isArray`
// @skjs-expect-error A type predicate ('x is T') is only supported as the top-level return type of a declared function or method signature
function isStrArray(x: string[] | number): x is string[] {
  return Array.isArray(x);
}

// 1h. `instanceof` on a nominal class (true proves C; false proves not-C on a
// nominal union — note: on `unknown`, `instanceof` does not narrow else branch,
// see negative tests below!)
class Cat {
  readonly meow: number = 1;
}
class Dog {
  readonly bark: number = 2;
}

// @skjs-expect-error A type predicate ('x is T') is only supported as the top-level return type of a declared function or method signature
function isCat(x: Cat | Dog): x is Cat {
  return x instanceof Cat;
}

// 1i. Non-first parameter subject
// @skjs-expect-error A type predicate ('x is T') is only supported as the top-level return type of a declared function or method signature
function isSecondStr(tag: number, x: unknown): x is string {
  void tag;
  return typeof x === "string";
}

// 1j. Nested closure inside a bodied predicate must not inherit active predicate
// @skjs-expect-error A type predicate ('x is T') is only supported as the top-level return type of a declared function or method signature
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

// 1l. `this is Sub` method on a nominal class hierarchy
class BaseNode {
  readonly kind: string = "base";
  // @skjs-expect-error A type predicate ('x is T') is only supported as the top-level return type of a declared function or method signature
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
// @skjs-expect-error Overload signature is not compatible with its implementation signature
function isTagged(x: unknown, tag: "s"): x is string;
// @skjs-expect-error Overload signature is not compatible with its implementation signature
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
// @skjs-expect-error A type predicate ('x is T') is only supported as the top-level return type of a declared function or method signature
function badAlwaysTrue(x: unknown): x is string {
  return true;
}

// 2b. Wrong type check: `typeof x === "number"` claimed as `x is string`
// @skjs-expect-error A type predicate ('x is T') is only supported as the top-level return type of a declared function or method signature
function badWrongType(x: unknown): x is string {
  return typeof x === "number";
}

// 2c. Opaque boolean expression
// @skjs-expect-error A type predicate ('x is T') is only supported as the top-level return type of a declared function or method signature
function badOpaqueBool(x: unknown, flag: boolean): x is string {
  void x;
  return flag;
}

// 2d. `||` widens true branch beyond target
// @skjs-expect-error A type predicate ('x is T') is only supported as the top-level return type of a declared function or method signature
function badOrTooWide(x: unknown): x is string {
  return typeof x === "string" || typeof x === "number";
}

// 2e. One branch returns `true` without narrowing
// @skjs-expect-error A type predicate ('x is T') is only supported as the top-level return type of a declared function or method signature
function badUnprovenBranch(x: unknown, flag: boolean): x is string {
  if (flag) {
    return true;
  }
  return typeof x === "string";
}

// --- 3. Unsound false-branch subtraction traps (CRITICAL SOUNDNESS) ---

// 3a. Narrower condition than claimed target: `isPositive(-1)` returns `false`,
// which would unsoundly exclude `number` from `number | string` in an `else`!
// @skjs-expect-error A type predicate ('x is T') is only supported as the top-level return type of a declared function or method signature
function badPositiveNumber(x: number | string): x is number {
  return typeof x === "number" && x > 0;
}

// 3b. Returning `false` unconditionally when subject could still be `target`
// @skjs-expect-error A type predicate ('x is T') is only supported as the top-level return type of a declared function or method signature
function badAlwaysFalse(x: string | number): x is string {
  void x;
  return false;
}

// 3c. Narrower target tested: `x === "a"` claimed as `x is string`
// @skjs-expect-error A type predicate ('x is T') is only supported as the top-level return type of a declared function or method signature
function badSubsetOfTarget(x: string | number): x is string {
  return x === "a";
}

// 3d. Early `return false` when subject could still be `target`
function badEarlyFalseWhenTarget(
  x: string | number,
  flag: boolean,
  // @skjs-expect-error A type predicate ('x is T') is only supported as the top-level return type of a declared function or method signature
): x is string {
  if (flag) {
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

// @skjs-expect-error A type predicate ('x is T') is only supported as the top-level return type of a declared function or method signature
function badCustomHasInstance(x: unknown): x is CustomHasInstance {
  return x instanceof CustomHasInstance;
}

// --- 4. Parameter reassignment, defaults, shadowing, try/finally, mutable fields ---

// 4a. Reassigning the predicate parameter does not change the caller's variable
// @skjs-expect-error A type predicate ('x is T') is only supported as the top-level return type of a declared function or method signature
function badReassignParam(x: unknown): x is string {
  x = "ok";
  return typeof x === "string";
}

// 4b. Predicate parameter with a default value (default substitutes locally, not at caller)
// @skjs-expect-error A type predicate ('x is T') is only supported as the top-level return type of a declared function or method signature
function badDefaultParam(x: string | undefined = "ok"): x is string {
  return typeof x === "string";
}

// 4c. Shadowing the parameter in an inner block must not spoof the predicate
// @skjs-expect-error A type predicate ('x is T') is only supported as the top-level return type of a declared function or method signature
function badShadowBlock(x: unknown): x is string {
  void x;
  {
    const x: string = "ok";
    return typeof x === "string";
  }
}

// 4d. Side-effecting `finally` mutating a mutable field on `this` after `try` returns
interface ReadyBox {
  readonly value: string;
}
class BadFinallyMutBox {
  value: string | null = null;
  // @skjs-expect-error A type predicate ('x is T') is only supported as the top-level return type of a declared function or method signature
  isReady(): this is ReadyBox {
    try {
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
  // @skjs-expect-error A type predicate ('x is T') is only supported as the top-level return type of a declared function or method signature
  isReady(): this is ReadyBox {
    if (this.value !== null) {
      sideEffect();
      return true;
    }
    return false;
  }
}

// 4f. Caller alias write after `this is ReadyBox` must invalidate mutable field
class MutableBox {
  value: string | null = null;
  // @skjs-expect-error A type predicate ('x is T') is only supported as the top-level return type of a declared function or method signature
  isReady(): this is ReadyBox {
    return this.value !== null;
  }
}

export function useMutableBoxAliasWrite(b: MutableBox): string {
  const alias: MutableBox = b;
  if (b.isReady()) {
    alias.value = null;
    // Currently unsoundly accepted (evalTypePred does not mark field refinement).
    return b.value;
  }
  return "";
}

// 4g. Receiverless `this: void` cannot satisfy `this is T`
// @skjs-expect-error A type predicate ('x is T') is only supported as the top-level return type of a declared function or method signature
function badReceiverlessThis(this: void): this is ReadyBox {
  return false;
}

// 4h. Async function cannot have a type predicate return type
// @skjs-expect-error A type predicate ('x is T') is only supported as the top-level return type of a declared function or method signature
// @ts-expect-error The return type of an async function must be the global Promise<T> type
async function badAsyncPred(x: unknown): x is string {
  return typeof x === "string";
}

// 4i. Returning non-boolean value in bodied predicate
// @skjs-expect-error A type predicate ('x is T') is only supported as the top-level return type of a declared function or method signature
function badReturnNonBool(x: unknown): x is string {
  void x;
  // @ts-expect-error Type of returned value is not assignable to the function's return type
  return 42;
}
