function uselessDefault(x: { f: number }): number {
  // @ts-expect-error Default is useless because field cannot be undefined
  const { f = 1 } = x;
  return f;
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
