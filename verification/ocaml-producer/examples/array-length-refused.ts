// `new Array(n)` makes an array of length `n` with no elements: holes,
// which an array type here promises it has not. The overlay reads `new
// Array` with no argument only.
function holes(n: number): number[] {
  return new Array(n);
}
