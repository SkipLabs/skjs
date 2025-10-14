function destructAlgebraic(
  x: { kind: "num"; f: number } | { kind: "str"; f: string },
): number {
  const { f } = x;
  // @ts-expect-error Invalid return type
  return f;
}

function destructAlgebraic2(
  x: { kind: "num"; f: number } | { kind: "str"; f: string },
): number | string {
  const { f } = x;
  return f;
}

function destructRest(x: { a: string; b: number; c: boolean }): {
  b: number;
  c: boolean;
} {
  // @ts-expect-error TODO: support rest destructuring
  const { a, ...rest } = x;
  return rest;
}
