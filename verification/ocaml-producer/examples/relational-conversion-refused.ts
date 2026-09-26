// An index read past an array's end is `undefined`, which TypeScript types as
// the element: `<` converts it to NaN, a comparison the model does not state.
export function negativeFirst(values: number[]): boolean {
  const first = values[0];
  return first < 0;
}
