// A generic module function called from another function needs a scheme
// elimination at the call, which module scope does not provide yet.
function same<T>(x: T): T {
  return x;
}
export function useSame(x: boolean): boolean {
  return same(x);
}
