function tuplePatternOnTop(): void {
  const objNoFields = {};
  const top = objNoFields["a"];
  // @skjs-expect-error Invalid tuple pattern
  const [_b] = top;
}
