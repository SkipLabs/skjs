// prettier-ignore
// A comma expression inside an interpolation (`${a, b}`): skjs has no comma
// operator, so the inline parse rejects it (stricter than tsc, consistent with
// skjs rejecting the comma operator everywhere). Was silently dropped before.
// @skjs-expect-error '}' expected
function commaInInterp(a: number, b: number): string { return `${a, b}`; }
