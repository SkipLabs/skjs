function uselessDefault(x: { f: number }): number {
  // @skjs-expect-warning This default is unreachable because the field cannot be 'undefined'
  const { f = 1 } = x;
  return f;
}

function uselessDefaultNull(x: { f: null }): void {
  // @skjs-expect-warning This default is unreachable because the field cannot be 'undefined'
  const { f = 1 } = x;
}

function uselessDefaultUnion(x: { f: number } | { f: string }): void {
  // @skjs-expect-warning This default is unreachable because the field cannot be 'undefined'
  const { f = true } = x;
}

function usefulDefault(
  x: { f: number } | { f?: string },
): number | string | boolean {
  const { f = true } = x;
  return f;
}

function defaultSameType(x: { f?: number }): number {
  const { f = 1 } = x;
  return f;
}

function defaultSameType2(x: { f: number | undefined }): number {
  const { f = 1 } = x;
  return f;
}

function defaultOtherType(x: { f?: number }): number | string {
  const { f = "a" } = x;
  return f;
}

function defaultOtherType2(x: { f: number | undefined }): number | string {
  const { f = "a" } = x;
  return f;
}

function defaultUndefined(x: { f?: number }): number {
  const { f = undefined } = x;
  return f ?? 0;
}

function defaultUndefined2(x: { f: number | undefined }): number {
  const { f = undefined } = x;
  return f ?? 0;
}

function optionalMeansUndefined(x: { f?: number }): number {
  const { f } = x;
  return f ?? 0;
}

function optionalMeansUndefinedWitness(x: { f: number }): number {
  const { f } = x;
  // @skjs-expect-warning This operator has no effect; the operand is never null or undefined
  return f ?? 0;
}
