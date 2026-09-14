function declaredRest(source: [number] | [number, string]): string[] {
  const [head, ...tail] = source;
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return tail;
}
function assignedRest<T>(source: [number] | [number, T]): T[] {
  let head: number | T | undefined = 0;
  let tail: T[] = [];
  // @skjs-expect-error Type is not assignable to the variable's type
  [head, ...tail] = source;
  return tail;
}
function incompatibleRest(source: [number] | [number, string]): void {
  let head: number | string | undefined = 0;
  let tail: boolean[] = [];
  // @ts-expect-error Type is not assignable to the variable's type
  [head, ...tail] = source;
}

function emptyRemainder(source: [number] | [number, string]): boolean[] {
  const [first, second, ...tail] = source;
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return tail;
}
