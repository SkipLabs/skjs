// prettier-ignore
// An octal escape in an INTERPOLATED template's text part (#826). tsc rejects
// it; the refactor validates every chunk. Pinned to the pre-refactor behavior.
function octalInPart(x: string): string {
  return `\1${x}`;
}
