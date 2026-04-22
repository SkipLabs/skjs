// Coverage tests for TVar growth (the subtyping machinery that grows
// free TVars during isSub). Each test exercises a distinct disjunct-
// handling path, either guarding current correctness or documenting a
// case that is currently broken.

type Maybe<T> = T | null;
type T3<X> = X | string | number;

// Regression test: per-disjunct precision. Some disjuncts of the
// argument are covered by non-TVar branches of the parameter type,
// some are not. Coverage filtering must grow only the uncovered parts
// into the TVar.
declare function partial<A>(x: A | string): A;
declare const numOrStr: number | string;

function testPartialCoverage(): number {
  return partial(numOrStr);
}

// Multi-disjunct alias: alias expansion produces three clauses
// (X | string | number); per-disjunct coverage picks the uncovered
// one.
declare function unwrapT3<A>(x: T3<A>): A;
declare const boolStrNum: boolean | string | number;

function testThreeWayAlias(): boolean {
  return unwrapT3(boolStrNum);
}

// Multi-TVar ordering: two independent TVars, each growing through an
// alias.
declare function pairUp<A, B>(x: Maybe<A>, y: Maybe<B>): [A, B];
declare const msStr: Maybe<string>;
declare const msNum: Maybe<number>;

function testMultiTVar(): [string, number] {
  return pairUp(msStr, msNum);
}

// Regression test: bare-TVar open branch. openTy is `A`, with no
// non-TVar clauses, so growTVars takes the "grow with full boundTy"
// fast path.
declare function identity<A>(x: A): A;

function testBareTVar(): string {
  return identity("hello");
}

// Regression test: constrained TVar, constraint satisfied. boundTy is
// `"hello"` and the TVar has upper bound `string`, so the constraint
// check passes and growth proceeds.
declare function takeStrBound<A extends string>(x: A): A;

function testConstraintPass(): string {
  return takeStrBound("hello");
}

// Regression test: constrained TVar, constraint violated. boundTy is
// `42` which doesn't satisfy `A extends string`; growth is skipped and
// the top-level isSub call rejects the call.
function testConstraintFail(): string {
  // @skjs-expect-error Invalid call
  return takeStrBound(42);
}

// Regression test: union-of-objects. Clauses::getObject returns None
// when there are multiple object clauses, so structural descent is
// bypassed. TFun::isSub handles the inference afterward without
// pre-seeding.
declare function taggedInline<A>(
  x: { tag: "a"; value: A } | { tag: "b"; value: A },
): A;
declare const taggedStr: { tag: "a"; value: string };

function testUnionOfObjects(): string {
  return taggedInline(taggedStr);
}
