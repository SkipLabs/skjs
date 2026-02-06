function restReadRemovedKey(x: { [k: string]: number; a: number }): number {
  const { a, ...r } = x;
  const ra: number | undefined = r["a"];
  return ra ?? 0;
}

function restWriteReintroducesKey(x: { [k: string]: number; a: number }): number {
  const { a, ...r } = x;
  const before: number | undefined = r["a"];
  r["a"] = 42;
  const after: number | undefined = r["a"];
  return (before ?? 0) + (after ?? 0);
}

function restReturnToStrictIndex(
  x: { [k: string]: number; a: number },
): { [k: string]: number } {
  const { a, ...r } = x;
  // @skjs-expect-error Invalid return type
  return r;
}

function restOnUnionReadIsUndefinedAware(
  x: { [k: string]: number; a: number } | { [k: string]: number; b: number },
): number {
  const { a, ...r } = x;
  const ra: number | undefined = r["a"];
  return ra ?? 0;
}
