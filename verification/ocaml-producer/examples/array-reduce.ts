// A method of Array.prototype, read through the array's prototype and called
// on the array: `reduce` with an initial value, at the element and the
// accumulator the call instantiates.
function sum(xs: number[]): number {
  return xs.reduce(
    (acc: number, x: number, i: number, all: readonly number[]): number => acc + x, 0);
}
