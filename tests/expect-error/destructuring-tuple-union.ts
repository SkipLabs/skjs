function assignedPrefix(source: [number] | [number, number]): number {
  let first: number = 0;
  // @skjs-expect-error Type is not assignable to the variable's type
  [first] = source;
  return first;
}
function declaredPrefix(source: [number] | [string, boolean]): number | string {
  const [first] = source;
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return first;
}
function missingPosition(source: [number] | [number, number]): number {
  const [first, second] = source;
  // @ts-expect-error Type of returned value is not assignable to the function's return type
  return second;
}
