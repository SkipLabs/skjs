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

// Depth 6, readonly depth 5, multi-element depth 5, and nested inner union
// of tuples all fall back to whole-tuple subtyping and fail for the same
// reason (#942).
declare function nest6<K extends [[[[[[0]]]]]]>(x: K): K;
function nestedTuplesDepth6(): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  const r = nest6([[[[[[0]]]]]]);
}

declare function nest5ro<
  K extends readonly [readonly [readonly [readonly [readonly [0]]]]],
>(x: K): K;
function nestedTuplesDepth5Readonly(): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  const r = nest5ro([[[[[0]]]]]);
}

declare function nest5multi<K extends [[[[[0, 1], [2, 3]]]]]>(x: K): K;
function nestedTuplesDepth5Multi(): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  const r = nest5multi([
    [
      [
        [
          [0, 1],
          [2, 3],
        ],
      ],
    ],
  ]);
}

declare function nestInnerUnion<K extends [[0, 1] | [2, 3]]>(x: K): K;
function nestedInnerUnionValid(): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  const r1 = nestInnerUnion([[0, 1]]);
  // @skjs-expect-error Argument is not assignable to the parameter's type
  const r2 = nestInnerUnion([[2, 3]]);
}

// Nested mismatches and unsound nested constraints must stay rejected.
function nestedMismatch(): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  const r = nest([
    [0, 1],
    [2, 9],
  ]);
}

function nestedDepth5Mismatch(): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  const r = nest5([[[[[1]]]]]);
}

declare function nestArms<K extends [[0, 1], [2, 3]] | [[4, 5], [6, 7]]>(
  x: K,
): K;
function nestedUnionArms(): void {
  const ok1 = nestArms([
    [0, 1],
    [2, 3],
  ]);
  const ok2 = nestArms([
    [4, 5],
    [6, 7],
  ]);
  // @skjs-expect-error Argument is not assignable to the parameter's type
  const cross = nestArms([
    [0, 1],
    [6, 7],
  ]);
}

function nestedInnerUnionCross(): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  const r = nestInnerUnion([[0, 3]]);
}

declare function nestBranded<K extends [[0, 1]] & { foo: string }>(x: K): K;
function nestedIntersectionMissingMember(): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  const r = nestBranded([[0, 1]]);
}

function nestedAbstractConstraint<L extends [[0, number]]>(
  f: <K extends L>(x: K) => K,
): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  const r = f([[0, 5]]);
}

declare function nestViaVar<B, K extends [[B]]>(b: B, x: K): K;
function nestedOpenConstraintVariable(): void {
  const good = nestViaVar("a", [["a"]]);
  // @skjs-expect-error Argument is not assignable to the parameter's type
  const bad = nestViaVar("a", [[1]]);
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

// A constraint whose positions are unions of literals: tsc infers K = [2, 3]
// (the argument's own element types), not the constraint's [0 | 2, 1 | 3]
// (#934). FIXME: SKJS pins K to the constraint's projection. Binding K to
// the narrower [2, 3] is rejected because SKJS checks mutable array-method
// parameters strictly, so [2, 3] is not a subtype of [0 | 2, 1 | 3] here
// ("would not be an error if this field were readonly"); the binding must
// satisfy the constraint, so K stays wide and the assignment below fails.
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
