/**
 * TypeScript keeps the guard's fact about `a.value` across the write through
 * `b`, although the two parameters may be one object: the aliased call below
 * returns null from a function declared to return a number. SKJS rejects the
 * program, and the verifier refuses TypeScript's claim, because no
 * distinct-location link separates two parameters.
 */
function aliasedWrite(
  a: { value: number | null },
  b: { value: number | null },
): number {
  if (a.value === null) return 0;
  b.value = null;
  const seen: number = a.value;
  return seen;
}
