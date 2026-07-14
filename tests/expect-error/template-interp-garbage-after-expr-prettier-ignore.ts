// prettier-ignore
// A second token after the interpolation expression (`${a b}`) is trailing
// garbage: tsc rejects it (`}` expected). Pinned to the pre-refactor behavior,
// which silently dropped it; the inline parse rejects it.
function garbageAfterExpr(a: number, b: number): string {
  return `${a b}`;
}
