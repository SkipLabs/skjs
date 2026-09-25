// sum.ts, Plus: an array method called inside a method.
class Summer {
  sum(xs: number[]): number {
    return xs.reduce((p: number, c: number): number => p + c, 0);
  }
}
export function use(xs: number[]): number {
  return new Summer().sum(xs);
}
