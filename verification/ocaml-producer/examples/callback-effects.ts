// The native call consumes the inferred type of a returned or bound callback.
// Its body is checked at definition, before either use of Array.prototype.map.
export function returnedCallback(xs: number[]): number[] {
  const make =
    () =>
    (value: number, _index: number, _array: readonly number[]): number =>
      value + 1;
  const next = make();
  return xs.map(next);
}

export function boundCallback(xs: number[]): number[] {
  const next = (
    value: number,
    _index: number,
    _array: readonly number[],
  ): number => value + 1;
  const bound = next.bind(undefined);
  return xs.map(bound);
}
