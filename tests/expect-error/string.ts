function const_plus_const(): string {
  const a: 'a' = 'a';
  const b: 'b' = 'b';
  // TODO: should not be an error
  // @ts-expect-error Invalid + operand
  return a + b;
}
