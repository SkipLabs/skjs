// Regression tests for the TVar constraint divergence fix.
// These exercise patterns that any comprehensive fix must handle
// correctly, testing sequential TVar constraining, recursive
// constraint inference, and type error detection.

type List<T> = null | { head: T; tail: List<T> };

// Fix E: version-independent seenSub
//
// tenv.seenSub keys on (subst.version, u1, u2). Removing version
// would make co-inductive cycle detection more aggressive.
// These tests verify that subtype checks produce correct results
// even when similar pairs are checked at different TVar states.

// Sequential constraining through multiple assignments
function fixE_sequentialConstraint<T>(x: T): List<T> {
  let result: List<T> = null;
  result = { head: x, tail: null };
  result = { head: x, tail: result };
  result = { head: x, tail: result };
  // @skjs-expect-error Invalid return type
  return result;
}

// Recursive list building should preserve type
function fixE_preserveType<T>(x: T, y: T): List<T> {
  let a: List<T> = { head: x, tail: null };
  let b: List<T> = { head: y, tail: a };
  return b;
}

// Fix A: memoize get — stale cache across tenv contexts
//
// subst.get() intersects stored_value with constraints. If we cache
// this result, the cache might become stale when tenv.seenInstantiate
// differs between call sites (value-typed TEnv resets per frame).

// Same recursive type at different nesting depths
function fixA_differentContexts<T>(x: List<T>, y: List<List<T>>): void {
  const a: List<T> = x;
  const b: List<List<T>> = y;
}

// Recursive type used in return position and assignment
function fixA_returnAndAssign<T>(x: T): List<T> {
  let result: List<T> = null;
  result = { head: x, tail: result };
  return result;
}

// Fix B: eager intersect in grow
//
// If grow() eagerly computes inter(newValue, constraint), this happens
// mid-isSub with potentially incomplete subst state.

// Multiple grow operations in sequence
function fixB_sequentialGrow<T>(x: T): List<T> {
  let result: List<T> = null;
  result = { head: x, tail: null };
  result = { head: x, tail: result };
  // @skjs-expect-error Invalid return type
  return result;
}

// Generic constraint with recursive type
function fixB_genericConstraint<T extends List<number>>(x: T): List<number> {
  return x;
}

// Deep nesting of recursive type
type Nested<T> = null | { data: T; child: Nested<T> };

function fixB_deepNest<T>(val: T): Nested<T> {
  return {
    data: val,
    child: { data: val, child: { data: val, child: null } },
  };
}
