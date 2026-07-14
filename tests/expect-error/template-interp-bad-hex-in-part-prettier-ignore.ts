// prettier-ignore
// An invalid \x escape in an INTERPOLATED template's text part (#826). tsc
// rejects it; the refactor decodes/validates every chunk. Pinned to the
// pre-refactor behavior, which left interpolated parts unvalidated.
function badHexInPart(x: string): string {
  return `a\xGGb${x}`;
}
