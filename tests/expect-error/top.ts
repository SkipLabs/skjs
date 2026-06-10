function tuplePatternOnTop(): void {
  const objNoFields = {};
  // @skjs-expect-error Property 'a' does not exist on this type
  const top = objNoFields["a"];
  const [_b] = top;
}
