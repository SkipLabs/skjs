// An array literal checked against a tuple-shaped generic constraint
// (issue #914, and the accept/reject half of #672).
//
// The literal's elements are fresh commitment type variables. When the
// committed tuple is checked against the constrained variable, growTVars used
// to seed EVERY element variable from the tuple's position-unioning methods
// (`pop(): T0 | T1 | ...`), sealing each sibling to the union of all
// positions; a literal whose every element matched its own position could
// still fail. Same-arity tuple pairs now seed from the positional fields
// only, which pair the elements one-to-one. Nested literals additionally
// check element-by-element against the constraint's positions, so the inner
// literals commit against their own positions too (#942).

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

// Nested tuple literals: each inner literal commits against its own
// constraint position rather than meeting the union of all positions through
// the tuple's number index and methods (#942).
declare function nest<K extends [[0, 1], [2, 3]]>(x: K): K;
function nestedTuples(): void {
  const r = nest([
    [0, 1],
    [2, 3],
  ]);
}

declare function nest3<K extends [[[0]]]>(x: K): K;
function nestedTuplesDepth3(): void {
  const r = nest3([[[0]]]);
}

// FIXME: TypeScript accepts this call. The faithfulness probe recurses at
// most kProjectionDepth levels into the constraint, so a deeper literal falls
// back to the whole-tuple check and the inner literals are rejected again
// (#942).
declare function nest5<K extends [[[[[0]]]]]>(x: K): K;
function nestedTuplesDepth5(): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  const r = nest5([[[[[0]]]]]);
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

// A union of tuples: an argument matching one arm exactly (tsc infers
// K = that arm).
function unionArmValidFirst(): void {
  const r = arms([0, 1]);
}
function unionArmValidSecond(): void {
  const r = arms([2, 3]);
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

// A mutable tuple constraint whose positions are unions of literals: tsc
// infers K = [2, 3], which is unsound because the callee can legally write `0`
// into `x[0]` per `[0 | 2, 1 | 3]` (see `mutateUnionLit` below). Because
// mutable tuples are invariant in SKJS, `[2, 3]` is not a subtype of
// `[0 | 2, 1 | 3]`, so SKJS keeps `K = [0 | 2, 1 | 3]` (contextual widening)
// and rejects the narrow `[2, 3]` annotation. Use a `readonly` tuple
// constraint (below) when covariant narrowing to the argument's own element
// types is desired (#934).
declare function unionLit<K extends [0 | 2, 1 | 3]>(x: K): K;
function unionLiteralConstraintKeepsArgument(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  // @skjs-expect-error-line2 Type '0 | 2'
  // @skjs-expect-error-line3 is not assignable to type '2'
  // @skjs-expect-error-line4 Value '0' is missing
  const r: [2, 3] = unionLit([2, 3]);
  const wide: [0 | 2, 1 | 3] = unionLit([2, 3]);
}

// An element outside its constraint position is still rejected.
function unionLiteralConstraintStillRejects(): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  // @skjs-expect-error-line2 Type '[1, 3]'
  // @skjs-expect-error-line3 is not assignable to type '[0 | 2, 1 | 3]'
  const r = unionLit([1, 3]);
}

// Soundness check for the mutable constraint above: the callee can legally
// mutate `x[0]` to `0` (per the constraint `[0 | 2, 1 | 3]`), so inferring
// `K = [2, 3]` as tsc does is unsound (r[0] would be 0 at runtime while typed
// `2`). SKJS keeps `K = [0 | 2, 1 | 3]` and rejects the narrow annotation.
function mutateUnionLit<K extends [0 | 2, 1 | 3]>(x: K): K {
  const zero: 0 = 0;
  x[0] = zero;
  return x;
}
function mutableConstraintPreventsUnsoundMutation(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  // @skjs-expect-error-line2 Type '0 | 2'
  // @skjs-expect-error-line3 is not assignable to type '2'
  // @skjs-expect-error-line4 Value '0' is missing
  const r: [2, 3] = mutateUnionLit([2, 3]);
  const wide: [0 | 2, 1 | 3] = mutateUnionLit([2, 3]);
}

// Readonly tuple constraints are covariant: the callee cannot mutate `x`, so
// inferring `K` as the argument's own element types is sound (#934).
declare function roUnionLit<K extends readonly [0 | 2, 1 | 3]>(x: K): K;
function roUnionLiteralConstraintKeepsArgument(): void {
  const r: [2, 3] = roUnionLit([2, 3]);
  const ro: readonly [2, 3] = roUnionLit([2, 3]);
}

// In a `let` context (non-mostPrecise), a fresh literal element still keeps
// its precise literal type when its constraint position expects a literal.
function roUnionLiteralConstraintLetContext(): void {
  let r = roUnionLit([2, 3]);
  const ok: [2, 3] = r;
}

// An element outside its readonly constraint position is still rejected.
function roUnionLiteralConstraintRejectsOutOfBounds(): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  // @skjs-expect-error-line2 Type '[1, 3]'
  // @skjs-expect-error-line3 is not assignable to type 'readonly [0 | 2, 1 | 3]'
  const r = roUnionLit([1, 3]);
}

// Mixed literal + non-literal position under a readonly constraint:
// position 0 expects a literal (`0 | 2` -> `2`), while position 1 expects
// `number` (not a literal, so `5` widens to `number`, matching tsc).
declare function roWidenUnion<K extends readonly [0 | 2, number]>(x: K): K;
function roMixedLiteralAndBase(): void {
  const r = roWidenUnion([2, 5]);
  const ok: [2, number] = r;
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  // @skjs-expect-error-line2 Full type 'number'
  // @skjs-expect-error-line3 is not assignable to specific type '5'
  const tooNarrow: [2, 5] = r;
}

// Non-literal variable elements under a union-of-base-types readonly constraint.
declare function roBaseUnion<
  K extends readonly [number | string, boolean | number],
>(x: K): K;
function roBaseUnionKeepsArgument(n: number, b: boolean): void {
  const r: [number, boolean] = roBaseUnion([n, b]);
}

// Subclass elements under a readonly tuple constraint.
class TupleAnimal {
  a: number = 0;
}
class TupleDog extends TupleAnimal {
  d: number = 1;
}
declare function roClassTuple<K extends readonly [TupleAnimal, TupleAnimal]>(
  x: K,
): K;
function roSubclassTupleKeepsArgument(d: TupleDog, a: TupleAnimal): void {
  const r: [TupleDog, TupleAnimal] = roClassTuple([d, a]);
}

// Nested readonly tuples: both outer and inner positions keep the argument's
// element types.
declare function roNestUnion<
  K extends readonly [readonly [0 | 2, 1 | 3], readonly [4 | 6, 5 | 7]],
>(x: K): K;
function roNestedTuplesKeepArgument(): void {
  const r: [[2, 3], [6, 7]] = roNestUnion([
    [2, 3],
    [6, 7],
  ]);
}

// Mixed readonly/mutable nesting: a mutable inner tuple cannot narrow because
// the callee can mutate `x[0][0] = 0`; a mutable outer tuple cannot narrow
// because the callee can replace `x[0] = [0, 1]`.
function mutateInnerTuple<K extends readonly [[0 | 2, 1 | 3]]>(x: K): K {
  const zero: 0 = 0;
  x[0][0] = zero;
  return x;
}
function roOuterMutableInnerStaysWide(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  // @skjs-expect-error-line2 Type '0 | 2'
  // @skjs-expect-error-line3 is not assignable to type '2'
  // @skjs-expect-error-line4 Value '0' is missing
  const r: [[2, 3]] = mutateInnerTuple([[2, 3]]);
  const wide: [[0 | 2, 1 | 3]] = mutateInnerTuple([[2, 3]]);
}

function mutateOuterTuple<K extends [readonly [0 | 2, 1 | 3]]>(x: K): K {
  x[0] = [0, 1];
  return x;
}
function mutableOuterRoInnerStaysWide(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  // @skjs-expect-error-line2 This would not be an error if this field were readonly
  const r: [[2, 3]] = mutateOuterTuple([[2, 3]]);
  const wide: [readonly [0 | 2, 1 | 3]] = mutateOuterTuple([[2, 3]]);
}

// Union of readonly tuples: each matching arm keeps the argument's elements,
// while cross-products stay rejected.
declare function roArmsUnion<
  K extends readonly [0 | 2, 1 | 3] | readonly [4 | 6, 5 | 7],
>(x: K): K;
function roUnionArmsKeepArgument(): void {
  const r1: [2, 3] = roArmsUnion([2, 3]);
  const r2: [6, 7] = roArmsUnion([6, 7]);
}
function roUnionArmsRejectCrossProduct(): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  const bad = roArmsUnion([2, 7]);
}

// Multi-parameter call with a readonly tuple constraint: same literal tuple
// infers `[2, 3]`, distinct tuples infer their union `[2, 3] | [0, 1]`.
declare function roTwoUnion<K extends readonly [0 | 2, 1 | 3]>(a: K, b: K): K;
function roTwoParamsSame(): void {
  const r: [2, 3] = roTwoUnion([2, 3], [2, 3]);
}
function roTwoParamsDistinct(): void {
  const r: [2, 3] | [0, 1] = roTwoUnion([2, 3], [0, 1]);
}
function roTwoParamsRejectBadSecond(): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  const r = roTwoUnion([2, 3], [0, 9]);
}

// Intersection of readonly and mutable tuple constraints must stay wide (the
// mutable part allows mutation inside the callee).
declare function roAndMutUnion<
  K extends readonly [0 | 2, 1 | 3] & [0 | 2, 1 | 3],
>(x: K): K;
function roAndMutIntersectionStaysWide(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  // @skjs-expect-error-line2 Type '0 | 2'
  // @skjs-expect-error-line3 is not assignable to type '2'
  // @skjs-expect-error-line4 Value '0' is missing
  const r: [2, 3] = roAndMutUnion([2, 3]);
  const wide: [0 | 2, 1 | 3] = roAndMutUnion([2, 3]);
}

// Aliasing soundness: if an uncommitted array literal variable is passed to a
// readonly-constrained generic that returns it at `K = [2, 3]`, mutating the
// original variable to `0` must be rejected so `r` cannot observe `0` at type
// `2`.
function roAliasedMutationAfterCall(): void {
  const arr = [2, 3];
  const r = roUnionLit(arr);
  const zero: 0 = 0;
  // @skjs-expect-error Type is not assignable to the assignment target's type
  // @skjs-expect-error-line2 Type '0'
  // @skjs-expect-error-line3 is not assignable to type '2'
  // @skjs-expect-error-line4 Value '0' is missing
  arr[0] = zero;
  const ok: [2, 3] = r;
}
function roAliasedMutationOutOfConstraint(): void {
  let saved: readonly [0 | 2, 1 | 3] = [0, 1];
  const save = <K extends readonly [0 | 2, 1 | 3]>(x: K): K => {
    saved = x;
    return x;
  };
  const arr = [2, 3];
  const r = save(arr);
  // @skjs-expect-error Type is not assignable to the assignment target's type
  arr[0] = 99;
}
