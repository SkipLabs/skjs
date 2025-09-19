function notSupportedDefault(x: { f: number }): number {
  // @ts-expect-error Construction not supported: default value in destructuring fields
  const { f = 1 } = x;
  return f;
}

function optionalMeansUndefined(x: { f?: number }): number {
  const { f } = x;
  // @ts-expect-error This operator is useless
  return f ?? 0;
}

function optionalMeansUndefinedWitness(x: { f: number }): number {
  const { f } = x;
  // @ts-expect-error This operator is useless
  return f ?? 0;
}
