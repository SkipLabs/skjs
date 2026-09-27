// A dense ordinary array can have an own constructor whose Symbol.species
// builds a non-array. The runtime controls supply such an input; callback
// purity alone does not establish these native result contracts.
export function mappedLength(xs: number[]): number {
  return xs.map((x: number): number => x).length;
}

export function filteredLength(xs: number[]): number {
  return xs.filter((x: number): boolean => x > 0).length;
}

export function slicedArray(xs: number[]): number[] {
  return xs.slice();
}
