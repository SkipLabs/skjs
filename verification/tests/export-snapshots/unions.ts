function unions(
  a: null | boolean,
  b: true | false,
  c: string | number,
  d: { value: boolean } | null,
  e: { value: boolean } | { value: null },
): boolean {
  return true;
}
