function shapes(
  a: { x: boolean; y: null },
  b: { value?: boolean },
  c: { readonly value: boolean },
  d: { value: { value: boolean } },
  e: { value: (x: boolean) => null },
): null {
  return null;
}
