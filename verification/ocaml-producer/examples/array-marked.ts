declare const marker: unique symbol;
type Marked = { readonly [marker]: true };
export function first(xs: [number, number] & Marked): number {
  return xs[0];
}
