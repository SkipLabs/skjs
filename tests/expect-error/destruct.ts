function destructAlgebraic(
  x: { kind: "num"; f: number } | { kind: "str"; f: string },
): number {
  // FIXME
  // @ts-expect-error f is already defined
  const { f } = x;
  return f;
}
