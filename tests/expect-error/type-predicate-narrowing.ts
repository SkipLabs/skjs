// Tests for user-defined type predicate narrowing and predicate subtyping
// (SkipLabs/skjs#582).

declare function isString(x: unknown): x is string;
declare function isNumber(x: unknown): x is number;
declare function isLitA(x: unknown): x is "a";
declare function isTrue(x: boolean): x is true;
declare function isSecondString(tag: number, x: unknown): x is string;
declare function isNonNull<T>(x: T | null | undefined): x is T;
declare function isTagged<T extends { kind: string }>(
  x: unknown,
  sample: T,
): x is T;
declare function isOptString(x?: string | number): x is string;
declare function isKind(x: unknown, kind: "str"): x is string;
declare function isKind(x: unknown, kind: "num"): x is number;

interface NodeBase {
  kind: string;
  isLeaf(): this is Leaf;
}
interface Leaf extends NodeBase {
  value: number;
}
interface Branch extends NodeBase {
  left: NodeBase;
}

interface Animal {
  name: string;
}
interface Dog extends Animal {
  bark(): void;
}
declare function isDog(x: Animal): x is Dog;

interface A {
  a: number;
}
interface B {
  b: string;
}
declare function isA(x: A | B): x is A;

// 1. Basic true-branch and false-branch narrowing
export function narrowStringOrNumber(x: string | number): number {
  if (isString(x)) {
    // @skjs-expect-error Property 'length' does not exist on this type
    return x.length;
  }
  return x + 1;
}

export function narrowStringOrNumberFalse(x: string | number): number {
  if (isString(x)) {
    return 0;
  }
  // @skjs-expect-error Operator '+' cannot be applied to these types
  return x + 1;
}

// 2. Negated predicate (!isString(x))
export function narrowNegated(x: string | number): number {
  if (!isString(x)) {
    // @skjs-expect-error Operator '+' cannot be applied to these types
    return x + 1;
  }
  return x.length;
}

export function narrowNegatedElse(x: string | number): number {
  if (!isString(x)) {
    return 0;
  }
  // @skjs-expect-error Property 'length' does not exist on this type
  return x.length;
}

// 3. Logical && and || composition
export function narrowLogicalAnd(x: unknown): number {
  // @skjs-expect-error Cannot access a property on type 'unknown'
  if (isString(x) && x.length > 0) {
    return x.length;
  }
  return 0;
}

export function narrowLogicalOr(x: string | number | boolean): string | number {
  if (isString(x) || isNumber(x)) {
    // @skjs-expect-error Type of returned value is not assignable to the function's return type
    return x;
  }
  return 0;
}

export function narrowLogicalOrFalse(x: string | number | boolean): boolean {
  if (isString(x) || isNumber(x)) {
    return true;
  }
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x;
}

// 4. Literal union false-branch subtraction
export function narrowLiteralUnionTrue(x: "a" | "b"): "a" {
  if (isLitA(x)) {
    // @skjs-expect-error Type of returned value is not assignable to the function's return type
    return x;
  }
  return "a";
}

export function narrowLiteralUnionFalse(x: "a" | "b"): "b" {
  if (isLitA(x)) {
    return "b";
  }
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x;
}

// 5. Boolean literal subtraction
export function narrowBooleanLiteralTrue(x: boolean): true {
  if (isTrue(x)) {
    // @skjs-expect-error Type of returned value is not assignable to the function's return type
    return x;
  }
  return true;
}

export function narrowBooleanLiteralFalse(x: boolean): false {
  if (isTrue(x)) {
    return false;
  }
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x;
}

// 6. Second parameter subject
export function narrowSecondParamTrue(x: string | number): number {
  if (isSecondString(1, x)) {
    // @skjs-expect-error Property 'length' does not exist on this type
    return x.length;
  }
  return 0;
}

export function narrowSecondParamFalse(x: string | number): number {
  if (isSecondString(1, x)) {
    return 0;
  }
  // @skjs-expect-error Operator '+' cannot be applied to these types
  return x + 1;
}

// 7. Optional parameter subject
export function narrowOptionalParamTrue(
  x: string | number | undefined,
): number {
  if (isOptString(x)) {
    // @skjs-expect-error Property access is not allowed on this type
    return x.length;
  }
  return 0;
}

export function narrowOptionalParamFalse(
  x: string | number | undefined,
): number | undefined {
  if (isOptString(x)) {
    return 0;
  }
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x;
}

// 8. Generic type predicate
export function narrowGenericNonNullConcrete(
  x: string | null | undefined,
): string {
  if (isNonNull(x)) {
    // @skjs-expect-error Type of returned value is not assignable to the function's return type
    return x;
  }
  return "";
}

export function narrowGenericNonNullConcreteFalse(
  x: string | null | undefined,
): null | undefined {
  if (isNonNull(x)) {
    return null;
  }
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x;
}

export function narrowGenericNonNullExplicit<U>(
  x: U | null | undefined,
  fallback: U,
): U {
  if (isNonNull<U>(x)) {
    // @skjs-expect-error Type of returned value is not assignable to the function's return type
    return x;
  }
  return fallback;
}

export function narrowGenericTarget<T extends { kind: string }>(
  x: unknown,
  sample: T,
): T {
  if (isTagged(x, sample)) {
    // @skjs-expect-error Type of returned value is not assignable to the function's return type
    return x;
  }
  return sample;
}

// 9. Method `this is T` narrowing (true and false branches)
export function narrowThisMethod(n: NodeBase): number {
  if (n.isLeaf()) {
    // @skjs-expect-error Property 'value' does not exist on this type
    return n.value;
  }
  const base: NodeBase = n;
  return base.kind.length;
}

export function narrowThisUnionTrue(n: Leaf | Branch): number {
  if (n.isLeaf()) {
    // @skjs-expect-error Property 'value' exists on some but not all members of the union type, so it may be absent
    return n.value;
  }
  return 0;
}

export function narrowThisUnionFalse(n: Leaf | Branch): NodeBase {
  if (n.isLeaf()) {
    return n;
  }
  // @skjs-expect-error Property 'left' exists on some but not all members of the union type, so it may be absent
  return n.left;
}

// 10. Overloaded type predicates
export function narrowOverloadStr(x: unknown): number {
  if (isKind(x, "str")) {
    // @skjs-expect-error Cannot access a property on type 'unknown'
    return x.length;
  }
  return 0;
}

export function narrowOverloadNum(x: unknown): number {
  if (isKind(x, "num")) {
    // @skjs-expect-error Operator '+' cannot be applied to these types
    return x + 1;
  }
  return 0;
}

// 11. Object union true and false narrowing
export function narrowObjectUnionTrue(x: A | B): number {
  if (isA(x)) {
    // @skjs-expect-error Property 'a' exists on some but not all members of the union type, so it may be absent
    return x.a;
  }
  return 0;
}

export function narrowObjectUnionFalse(x: A | B): number {
  if (isA(x)) {
    return 0;
  }
  // @skjs-expect-error Property 'b' exists on some but not all members of the union type, so it may be absent
  return x.b.length;
}

// 12. Open supertype: true narrows to subtype, false keeps supertype
export function narrowOpenSupertype(x: Animal): string {
  if (isDog(x)) {
    // @skjs-expect-error Property 'bark' does not exist on this type
    x.bark();
    return x.name;
  }
  return x.name;
}

// 13. Disjoint target narrows true branch to never, false branch unchanged
export function narrowDisjoint(x: number): number {
  if (isString(x)) {
    // @skjs-expect-error Type of value is not assignable to the variable's type annotation
    const n: never = x;
    return n;
  }
  return x + 1;
}

// 14. Subtyping: predicate assignable to plain boolean function
interface GuardHolder {
  check(x: unknown): x is string;
}
interface PlainHolder {
  check(x: unknown): boolean;
}
export function predicateToBoolean(h: GuardHolder): PlainHolder {
  return h;
}

// 15. Subtyping: plain boolean function NOT assignable to predicate
// FIXME(#582): predicate subtyping is not yet enforced; SKJS silently accepts.
export function booleanToPredicate(h: PlainHolder): GuardHolder {
  return h;
}

// 16. Subtyping: incompatible predicate targets rejected
// FIXME(#582): predicate subtyping is not yet enforced; SKJS silently accepts.
interface NumGuardHolder {
  check(x: unknown): x is number;
}
export function mismatchedPredicateTarget(h: GuardHolder): NumGuardHolder {
  return h;
}

// 17. Subtyping: narrower predicate target is NOT assignable to wider target
// (unsound for false-branch subtraction: `x is "a"` returning false does not
// rule out `"b"`, so a caller expecting `x is string` would unsoundly exclude
// all strings in the else branch).
// FIXME(#582): predicate subtyping is not yet enforced; SKJS silently accepts.
interface LitAGuardHolder {
  check(x: unknown): x is "a";
}
export function narrowerPredicateTarget(h: LitAGuardHolder): GuardHolder {
  return h;
}

// 18. Subtyping: predicate with different subject index rejected
// FIXME(#582): predicate subtyping is not yet enforced; SKJS silently accepts.
interface FirstGuard {
  check(a: unknown, b: unknown): a is string;
}
interface SecondGuard {
  check(a: unknown, b: unknown): b is string;
}
export function mismatchedPredicateSubject(h: SecondGuard): FirstGuard {
  return h;
}

// 19. Subtyping: this-predicate vs param-predicate rejected
// FIXME(#582): predicate subtyping is not yet enforced; SKJS silently accepts.
interface ThisGuard {
  check(x: unknown): this is Leaf;
}
interface ParamGuard {
  check(x: unknown): x is Leaf;
}
export function mismatchedThisVsParam(h: ParamGuard): ThisGuard {
  return h;
}

// 20. Soundness: captured mutable local is NOT narrowed across a call
export function capturedMutableNotNarrowed(init: string | number): number {
  let x: string | number = init;
  const reset = (): void => {
    x = 42;
  };
  if (isString(x)) {
    reset();
    // @skjs-expect-error Property 'length' does not exist on this type
    return x.length;
  }
  return 0;
}

// 21. Soundness: captured mutable receiver is NOT narrowed by `this is T`
export function capturedMutableThisNotNarrowed(init: NodeBase): number {
  let n: NodeBase = init;
  const reset = (): void => {
    n = init;
  };
  if (n.isLeaf()) {
    reset();
    // @skjs-expect-error Property 'value' does not exist on this type
    return n.value;
  }
  return 0;
}

// 22. Union of two predicate functions with different targets must NOT narrow
// the else branch (soundness: if f is isString and x is 42, f(42) is false).
export function unionPredicateNotNarrowedFalse(
  x: string | number | boolean,
  cond: boolean,
): boolean {
  const fn = cond ? isString : isNumber;
  if (fn(x)) {
    return true;
  }
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x;
}
