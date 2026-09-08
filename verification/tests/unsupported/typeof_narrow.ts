/**
 * Future narrowing example using successive typeof tests over a union.
 * String/number types and these tests remain outside the current source
 * fragment.
 */
function describe(x: string | number | null): string {
  if (typeof x === "string") {
    return x;
  }
  if (typeof x === "number") {
    return "a number";
  }
  return "null";
}
