function tuplePatternOnTop(): void {
  const objNoFields = {};
  // @skjs-expect-error Unbound field: a
  const top = objNoFields["a"];
  const [_b] = top;
}
