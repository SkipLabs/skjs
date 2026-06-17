// Accessing a field that is present in some — but not all — branches of a
// union object type. The access is unsafe (a value of a branch that lacks the
// field has it `undefined` at runtime), so it is flagged; but SKJS recovers
// with the type from the branches where the field IS present, so one such
// access does not cascade. A field present in NO branch stays the ordinary
// "does not exist" error.

// 'a' is present in one branch: flagged, recovered as `number` (so the return
// type-checks — a wrong recovery type would surface a second error here).
function readSome(x: { a: number } | { b: string }): number {
  // @skjs-expect-error Property 'a' exists on some but not all members of the union type, so it may be absent
  return x.a;
}

// 'zzz' is present in no branch: ordinary not-found error.
function readNone(x: { a: number } | { b: string }): number {
  // @skjs-expect-error Property 'zzz' does not exist on this type
  return x.zzz;
}

// Several keys partial at once ('a' in one branch, 'b' in the other): reported
// as a single combined diagnostic, not one per key, and recovered as the union
// of the present-branch types.
function readSomePlural(
  x: { a: number; c: 0 } | { b: string; c: 0 },
  k: "a" | "b",
): number | string {
  // @skjs-expect-error Properties 'a', 'b' exist on some but not all members of the union type, so they may be absent
  return x[k];
}
