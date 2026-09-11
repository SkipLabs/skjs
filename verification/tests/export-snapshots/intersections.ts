function records(
  c: { value: null } & { value: boolean },
  d: { value: boolean } & { value: true | false },
  e: { x: boolean } & { y: null },
): null {
  return null;
}
function arrows(f: ((x: true) => null) & ((x: false) => null)): null {
  return f(true);
}
