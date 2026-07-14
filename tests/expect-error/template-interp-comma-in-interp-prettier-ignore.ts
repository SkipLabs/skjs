// prettier-ignore
// A comma expression inside an interpolation (`${a, b}`): skjs has no comma
// operator, so the inline parse rejects it (stricter than tsc). Pinned to the
// pre-refactor behavior, which silently dropped the tail.
function commaInInterp(a: number, b: number): string {
  return `${a, b}`;
}
