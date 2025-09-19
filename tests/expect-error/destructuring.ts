function uselessDefault(x: { f: number }): number {
  // @ts-expect-error Default is useless because field cannot be undefined
  const { f = 1 } = x;
  return f;
}

function uselessDefaultNull(x: { f: null }): void {
  // @ts-expect-error Default is useless because field cannot be undefined
  const { f = 1 } = x;
}

function uselessDefaultUnion(x: { f: number } | { f: string }): void {
  // @ts-expect-error Default is useless because field cannot be undefined
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
  // FIXME: cannot be undefined
  // @ts-expect-error Invalid return type
  return f;
}

function defaultSameType2(x: { f: number | undefined }): number {
  const { f = 1 } = x;
  // FIXME: cannot be undefined
  // @ts-expect-error Invalid return type
  return f;
}

function defaultOtherType(x: { f?: number }): number | string {
  const { f = "a" } = x;
  // FIXME: cannot be undefined
  // @ts-expect-error Invalid return type
  return f;
}

function defaultOtherType2(x: { f: number | undefined }): number | string {
  const { f = "a" } = x;
  // FIXME: cannot be undefined
  // @ts-expect-error Invalid return type
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
  // @ts-expect-error This operator is useless
  return f ?? 0;
}
