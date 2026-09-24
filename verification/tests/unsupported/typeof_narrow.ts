/**
 * Future narrowing example using an "object" typeof test over a union.
 * That test also holds for null, so it is no shape test; the `typeof` result
 * as a string value remains outside the current source fragment.
 */
function describe(x: { name: string } | number | null): string {
  if (typeof x === "object") {
    return "an object or null";
  }
  return "a number";
}
