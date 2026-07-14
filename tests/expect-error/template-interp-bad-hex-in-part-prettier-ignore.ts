// prettier-ignore
// An invalid \x escape in an INTERPOLATED template's text part (#826): the
// refactor validates every chunk, so it is rejected like everywhere else. Was
// unvalidated (accepted) before the refactor.
// @skjs-expect-error Hexadecimal digit expected
function badHexInPart(x: string): string { return `a\xGGb${x}`; }
