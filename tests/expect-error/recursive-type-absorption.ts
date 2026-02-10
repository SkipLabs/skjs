// Tests for recursive type alias patterns where the absorption law's
// syntactic containment check (containsType) may fail to simplify,
// even though simplification is semantically valid.
//
// The absorption law checks: (A | B) & B = B via syntactic containment.
// These tests exercise patterns where the stored TVar value and the
// constraint have different structural representations.

// Case 1: Expanded-vs-unexpanded mismatch
//
// grow() stores the expanded form of a recursive alias via diff(),
// which calls expand(None()). The constraint remains as an unexpanded
// TSInst. containsType(expanded_clauses, TSInst) returns false because
// the insts sets don't match.

type List<T> = null | { head: T; tail: List<T> };

function expandedVsUnexpanded<T>(x: T): List<T> {
  let result: List<T> = null;
  result = { head: x, tail: result };
  return result;
}

// Case 2: Multiple constraints via mutual recursion
//
// When inter_ encounters a TVar as one operand (TTypeInter.sk:63-69),
// it adds the other type as a constraint via addConstraint.
// A TVar with constraints {C1, C2} forces get() to compute
// inter(inter(stored, C1), C2). Even if absorption catches the first
// intersection, the second may re-expand.

type Even<T> = null | { val: T; next: Odd<T> };
type Odd<T> = { val: T; next: Even<T> };

function multipleConstraints<T>(a: Even<T>, b: Odd<T>): void {
  const x: Even<T> = a;
  const y: Odd<T> = b;
}

function multipleConstraintsBuild<T>(val: T, b: Odd<T>): Even<T> {
  return { val: val, next: b };
}

// Case 3: Nested expansion depth mismatch
//
// When a recursive type is expanded at different depths in different
// contexts, the stored value may have 2 levels of expansion while
// the constraint has 1 level. These are semantically equal but
// structurally different, so containsType returns false.

type Tree<T> = null | { val: T; left: Tree<T>; right: Tree<T> };

function nestedExpansion<T>(root: Tree<T>, branch: Tree<T>): Tree<T> {
  let r = root;
  if (r !== null) {
    return { val: r.val, left: branch, right: r.right };
  }
  return root;
}

function nestedExpansionDeep<T>(t: Tree<T>): Tree<T> {
  let node = t;
  if (node !== null) {
    let left = node.left;
    if (left !== null) {
      // @skjs-expect-error Invalid return type
      return {
        val: node.val,
        left: { val: left.val, left: left.left, right: left.right },
        right: node.right,
      };
    }
  }
  return t;
}

// Positive: building nested recursive values
function wrongRecursiveType<T>(x: T): List<T> {
  // @skjs-expect-error Invalid annotation
  const result: List<T> = { head: x, tail: { head: x, tail: null } };
  return result;
}
