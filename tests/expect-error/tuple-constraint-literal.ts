// An array literal checked against a tuple-shaped generic constraint
// (issue #914, and the accept/reject half of #672).
//
// The literal's elements are fresh commitment type variables. When the
// committed tuple is checked against the constrained variable, growTVars used
// to seed EVERY element variable from the tuple's position-unioning methods
// (`pop(): T0 | T1 | ...`), sealing each sibling to the union of all
// positions; a literal whose every element matched its own position could
// still fail. Same-arity tuple pairs now seed from the positional fields
// only, which pair the elements one-to-one.

// Exact match: tsc infers K = [0, 1].
declare function exact<K extends [0, 1]>(x: K): K;
function exactMatch(): void {
  const r = exact([0, 1]);
}

// Contextual widening: the literal's `5` satisfies the constraint's `number`.
declare function widen<K extends [0, number]>(x: K): K;
function widenedElement(): void {
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
  const r = roExact([0, 1]);
}

declare function roWiden<K extends readonly [0, number]>(x: K): K;
function readonlyWidenedElement(): void {
  const r = roWiden([0, 5]);
}

// FIXME: TypeScript accepts this call. The outer positions pair one-to-one,
// but the uncommitted inner literals still fail the constraint's own
// position-unioning members, so SKJS rejects nested tuple literals (#942).
declare function nest<K extends [[0, 1], [2, 3]]>(x: K): K;
function nestedTuples(): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  const r = nest([
    [0, 1],
    [2, 3],
  ]);
}

// The same variable used for two parameters: two equal tuples agree.
declare function two<K extends [0, 1]>(a: K, b: K): K;
function twoParametersAgree(): void {
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
// shared element type: arrays have no positional fields, so their method
// members remain the seeding channel.
type NumbersOrString = number[] | string;
declare function arrayConstrained<S extends NumbersOrString>(x: S): S;
function arrayConstraintWidens(): void {
  const r = arrayConstrained([1, 2, 3]);
}

// The bound variable flows on: the result satisfies the constraint's tuple,
// and a mismatched annotation is still rejected.
declare function flow<K extends [0, 1]>(x: K): K;
function resultFlowsToAnnotation(): void {
  const ok: [0, 1] = flow([0, 1]);
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const bad: [1, 0] = flow([0, 1]);
}

// Positional-only seeding must not loosen what a constraint means. The cases
// below have no tuple that faithfully summarises the constraint, and each
// must stay rejected.

// A union of tuples: a cross-product matching neither arm.
declare function arms<K extends [0, 1] | [2, 3]>(x: K): K;
function unionArmCrossProduct(): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  const r = arms([0, 3]);
}

// An intersection with a member the literal does not have -- `foo` would
// otherwise be readable but absent at runtime.
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

// A constraint that is itself an abstract type parameter: any same-shaped
// literal must not stand in for L.
function abstractConstraint<L extends [0, number]>(
  f: <K extends L>(x: K) => K,
): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  const r = f([0, 5]);
}

// A constraint naming a still-open inference variable is checked against
// what that variable was inferred to be, not grown to admit the literal.
declare function viaVar<B, K extends [B]>(b: B, x: K): K;
function openConstraintVariable(): void {
  const good = viaVar("a", ["a"]);
  // @skjs-expect-error Argument is not assignable to the parameter's type
  const bad = viaVar("a", [1]);
}
