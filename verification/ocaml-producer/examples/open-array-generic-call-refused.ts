// `x instanceof Array` on `unknown` finds that the value owns an array's
// store, not that it is an array of `Array.prototype`: passed where a
// generic call expects an array, it is refused by that reason.
declare function size<A>(a: Array<A>): number;

export function sizeOf(x: unknown): number {
  if (x instanceof Array) {
    return size(x);
  }
  return 0;
}
