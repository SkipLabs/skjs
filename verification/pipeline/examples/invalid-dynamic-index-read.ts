// A runtime string may name an absent property.
function assumeDynamicPresent(
  x: { readonly [key: string]: boolean },
  key: string,
): boolean {
  return x[key];
}
