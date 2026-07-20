// An array literal checked against a tuple-shaped generic constraint
// (issue #914, and the accept/reject half of #672).
//
// The literal's elements are fresh commitment type variables. Committing the
// whole tuple and then checking it against the constrained variable ran a
// structural pre-seed that grew EVERY element variable from the tuple's
// position-unioning methods (`pop(): T0 | T1 | ...`), sealing each sibling to
// the union of all positions. Checking element-by-element against the
// constraint's tuple instead keeps the positions apart.

// Exact match: tsc infers K = [0, 1].
declare function exact<K extends [0, 1]>(x: K): K;
function exactMatch(): void {
  // FIXME: TypeScript accepts this call. Committing the whole tuple and then
  // checking it against the constrained variable seals every element
  // commitment variable to the union of all tuple positions, so the
  // constraint check fails on a literal that matches it (#914, #672).
  // @skjs-expect-error Argument is not assignable to the parameter's type
  const r = exact([0, 1]);
}

// Contextual widening: the literal's `5` satisfies the constraint's `number`.
declare function widen<K extends [0, number]>(x: K): K;
function widenedElement(): void {
  // FIXME: TypeScript accepts this call. Committing the whole tuple and then
  // checking it against the constrained variable seals every element
  // commitment variable to the union of all tuple positions, so the
  // constraint check fails on a literal that matches it (#914, #672).
  // @skjs-expect-error Argument is not assignable to the parameter's type
  const r = widen([0, 5]);
}

// Same value in both positions: never conflated to begin with, and still fine.
declare function same<K extends [0, 0]>(x: K): K;
function sameValueElements(): void {
  const r = same([0, 0]);
}

// More than two positions.
declare function three<K extends [0, 1, 2]>(x: K): K;
function threePositions(): void {
  // FIXME: TypeScript accepts this call. Committing the whole tuple and then
  // checking it against the constrained variable seals every element
  // commitment variable to the union of all tuple positions, so the
  // constraint check fails on a literal that matches it (#914, #672).
  // @skjs-expect-error Argument is not assignable to the parameter's type
  const r = three([0, 1, 2]);
}

// A union constraint position accepts either literal.
declare function unionElt<K extends [0 | 1, 0 | 1]>(x: K): K;
function unionConstraintPosition(): void {
  const r = unionElt([0, 1]);
}

// readonly tuple constraints take the same path.
declare function roExact<K extends readonly [0, 1]>(x: K): K;
function readonlyExactMatch(): void {
  // FIXME: TypeScript accepts this call. Committing the whole tuple and then
  // checking it against the constrained variable seals every element
  // commitment variable to the union of all tuple positions, so the
  // constraint check fails on a literal that matches it (#914, #672).
  // @skjs-expect-error Argument is not assignable to the parameter's type
  const r = roExact([0, 1]);
}

declare function roWiden<K extends readonly [0, number]>(x: K): K;
function readonlyWidenedElement(): void {
  // FIXME: TypeScript accepts this call. Committing the whole tuple and then
  // checking it against the constrained variable seals every element
  // commitment variable to the union of all tuple positions, so the
  // constraint check fails on a literal that matches it (#914, #672).
  // @skjs-expect-error Argument is not assignable to the parameter's type
  const r = roWiden([0, 5]);
}

// Nested tuples: the inner literals commit against the inner constraint
// positions.
declare function nest<K extends [[0, 1], [2, 3]]>(x: K): K;
function nestedTuples(): void {
  // FIXME: TypeScript accepts this call. Committing the whole tuple and then
  // checking it against the constrained variable seals every element
  // commitment variable to the union of all tuple positions, so the
  // constraint check fails on a literal that matches it (#914, #672).
  // @skjs-expect-error Argument is not assignable to the parameter's type
  const r = nest([
    [0, 1],
    [2, 3],
  ]);
}

// The same variable used for two parameters: both literals check against the
// constraint's positions, so two equal tuples agree.
declare function two<K extends [0, 1]>(a: K, b: K): K;
function twoParametersAgree(): void {
  // FIXME: TypeScript accepts this call. Committing the whole tuple and then
  // checking it against the constrained variable seals every element
  // commitment variable to the union of all tuple positions, so the
  // constraint check fails on a literal that matches it (#914, #672).
  // @skjs-expect-error Argument is not assignable to the parameter's type
  const r = two([0, 1], [0, 1]);
}

// ...and two different tuples still do not.
function twoParametersDisagree(): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  const r = two([0, 1], [1, 0]);
}

// A genuinely mismatched position is still rejected, and the diagnostic still
// names both tuples rather than a single element.
declare function mismatch<K extends [0, 1]>(x: K): K;
function mismatchedElement(): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  // @skjs-expect-error-line2 Type '[0, 2]'
  // @skjs-expect-error-line3 is not assignable to type '[0, 1]'
  const r = mismatch([0, 2]);
}

// An element of the wrong primitive kind is rejected too.
declare function kinds<K extends [0, "a"]>(x: K): K;
function mismatchedElementKind(): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  // @skjs-expect-error-line2 Type '[0, "b"]'
  // @skjs-expect-error-line3 is not assignable to type '[0, "a"]'
  const r = kinds([0, "b"]);
}

// Arity mismatch keeps the whole-tuple diagnostic.
declare function arity<K extends [0, 1, 2]>(x: K): K;
function arityMismatch(): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  const r = arity([0, 1]);
}

// An array-shaped constraint still widens the literal's elements to the
// shared element type rather than checking them position-by-position.
type NumbersOrString = number[] | string;
declare function arrayConstrained<S extends NumbersOrString>(x: S): S;
function arrayConstraintWidens(): void {
  const r = arrayConstrained([1, 2, 3]);
}

// The bound variable flows on: the result is the constraint's tuple, so a
// narrower annotation is still rejected.
declare function flow<K extends [0, 1]>(x: K): K;
function resultFlowsToAnnotation(): void {
  // FIXME: TypeScript accepts this call. Committing the whole tuple and then
  // checking it against the constrained variable seals every element
  // commitment variable to the union of all tuple positions, so the
  // constraint check fails on a literal that matches it (#914, #672).
  // @skjs-expect-error Argument is not assignable to the parameter's type
  const ok: [0, 1] = flow([0, 1]);
  // FIXME: the call itself is rejected for the same reason as above; only the
  // annotation mismatch below it should survive (#914, #672).
  // @skjs-expect-error Argument is not assignable to the parameter's type
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const bad: [1, 0] = flow([0, 1]);
}

// The element-wise path may only be taken when the constraint's tuple
// projection means exactly what the constraint means. The cases below are the
// ones where it does not, and each must keep reaching the whole-tuple check.

// A union of tuples projects position-wise (`[0, 1] | [2, 3]` becomes
// `[0 | 2, 1 | 3]`), which would admit a cross-product matching neither arm.
declare function arms<K extends [0, 1] | [2, 3]>(x: K): K;
function unionArmCrossProduct(): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  const r = arms([0, 3]);
}

// An intersection projects to its positions alone, dropping members the
// literal does not have -- `foo` would otherwise be readable but absent.
declare function branded<K extends [0, 1] & { foo: string }>(x: K): K;
function intersectionMissingMember(): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  const r = branded([0, 1]);
}

// ...including when the missing member is callable.
declare function withMethod<K extends [0, 1] & { m: () => string }>(x: K): K;
function intersectionMissingMethod(): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  const r = withMethod([0, 1]);
}

// A constraint that is itself an abstract type parameter cannot be projected:
// binding through it would let any same-shaped literal stand in for L.
function abstractConstraint<L extends [0, number]>(
  f: <K extends L>(x: K) => K,
): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  const r = f([0, 5]);
}

// A constraint naming a still-open inference variable must be checked against
// what that variable was inferred to be, not grown to admit the literal.
declare function viaVar<B, K extends [B]>(b: B, x: K): K;
function openConstraintVariable(): void {
  const good = viaVar("a", ["a"]);
  // @skjs-expect-error Argument is not assignable to the parameter's type
  const bad = viaVar("a", [1]);
}
