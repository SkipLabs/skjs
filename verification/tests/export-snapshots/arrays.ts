function arrayClaims(values: number[]): readonly (number | string)[] {
  return values;
}
function tupleClaims(values: readonly [number, string]): number {
  return values[0];
}
