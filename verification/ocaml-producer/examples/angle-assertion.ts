// `<T>e` is the older spelling of `e as T`: an obligation on the operand,
// never a fact; `<const>e` is `e as const`.
function widened(x: number): unknown {
  const y: unknown = <unknown>x;
  return y;
}
function pinned(): readonly [1, 2] {
  return <const>[1, 2];
}
