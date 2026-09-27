// Original sparse-result target: species can return a non-array, so the
// native contract must justify construction before it can promise a length.
export function mappedLength(xs: number[]): number {
  return xs.map((x: number): number => {
    xs.pop();
    return x;
  }).length;
}

// The original repair-corpus example: tuple methods survive a typeof branch.
export function testTupleArrayMethod(x: [number, string] | number): number {
  if (typeof x === "object") {
    return x.map((v: number | string) => v).length;
  } else {
    return x;
  }
}
