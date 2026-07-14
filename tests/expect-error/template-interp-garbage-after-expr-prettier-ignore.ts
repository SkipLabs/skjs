// prettier-ignore
// A second token after the interpolation expression (`${a b}`) is trailing
// garbage; the inline parse requires the closing `}` and rejects it (tsc: `}`
// expected). Was silently dropped before the refactor.
// @skjs-expect-error '}' expected
function garbageAfterExpr(a: number, b: number): string { return `${a b}`; }
