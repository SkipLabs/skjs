// Index access on a union of object types resolves a key only when *every*
// branch can resolve it (as a named field or via a covering index signature);
// the result is the union of the per-branch types. These pin the all-branches
// read semantics that must survive the removal of TObject::getFields /
// TFields::union (which currently flatten the branches into one TFields).

// Key present as a named field in both branches: result unions both types.
function bothBranchesField(x: { a: number } | { a: string }): number | string {
  return x["a"];
}

// Key is a named field in one branch and covered by an index in the other.
// SKJS resolves it, but the index contributes `| undefined` (a value of the
// indexed branch need not have the key), so the result is `number | undefined`
// — stricter than TypeScript, which yields `number`.
function fieldOrIndex(
  x: { a: number } | { [k: string]: number },
): number | undefined {
  return x["a"];
}

// Key present in one branch only: the access is flagged (it may be absent — a
// value of the other branch has no such property) but recovers as the present
// branch's type (#716).
function notInAllBranches(x: { a: number } | { b: string }): number {
  // @skjs-expect-error Property 'a' exists on some but not all members of the union type, so it may be absent
  return x["a"];
}
