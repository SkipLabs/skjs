
function tuplePatternOnTop(): void {
    const objNoFields = {};
    const top = objNoFields['a'];
    // @ts-expect-error Invalid tuple pattern
    const [_b] = top;
}
