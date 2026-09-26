// `<number>u` asserts what nothing establishes of an unknown value.
function narrowed(u: unknown): number {
  return <number>u;
}
