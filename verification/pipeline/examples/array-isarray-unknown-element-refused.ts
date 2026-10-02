// `Array.isArray` on `unknown` narrows nothing: an element read of the value
// is refused by that reason.
export function first(x: unknown): unknown {
  if (Array.isArray(x)) {
    return x[0];
  }
  return undefined;
}
