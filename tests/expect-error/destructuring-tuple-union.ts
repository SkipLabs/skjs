function assignedPrefix(source: [number] | [number, number]): number {
  let first: number = 0;
  [first] = source;
  return first;
}
function declaredPrefix(source: [number] | [string, boolean]): number | string {
  const [first] = source;
  return first;
}
function missingPosition(source: [number] | [number, number]): number {
  const [first, second] = source;
  // @ts-expect-error Type of returned value is not assignable to the function's return type
  return second;
}
