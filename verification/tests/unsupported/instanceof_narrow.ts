/**
 * Future narrowing example using an `instanceof` test of a constructor. The
 * model gives an object no identity of the constructor that made it, so the
 * test has no lowering yet (DESIGN.md, "Guards").
 */
function describe(
  x: { a: number } | number,
  C: new () => { a: number },
): string {
  if (x instanceof C) {
    return "made by C";
  }
  return "something else";
}
