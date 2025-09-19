function notSupportedDefault(x: { f: number }): number {
  // @ts-expect-error Construction not supported: default value in destructuring fields
  const { f = 1 } = x;
  return f;
}
