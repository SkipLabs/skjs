// sum.ts, Minus: a local closure without a return annotation, an explicit
// type argument to reduce, and `??` on its result.
export function minus(xs: [number, number][]): number {
  const acc = (p: number | null, c: [number, number]) => {
    return p !== null ? p - c[1] : c[1];
  };
  return xs.sort().reduce<number | null>(acc, null) ?? 0;
}
