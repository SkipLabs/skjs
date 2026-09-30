// A field found holding an object holds some value other than `undefined`
// until a step may write it: a call between the test and the read may write
// `undefined` there.
export function afterCall(
  x: { f?: { a: number } },
  g: () => void,
): { a: number } {
  if (x.f) {
    g();
    return x.f;
  }
  return { a: 0 };
}
