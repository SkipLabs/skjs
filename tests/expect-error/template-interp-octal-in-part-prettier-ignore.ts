// prettier-ignore
// An octal escape in an INTERPOLATED template's text part (#826): validated by
// the refactor and rejected. Was unvalidated (accepted) before.
// @skjs-expect-error Octal escape sequences are not allowed
function octalInPart(x: string): string { return `\1${x}`; }
