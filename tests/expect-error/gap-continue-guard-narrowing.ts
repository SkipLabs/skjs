// A `continue` guard should narrow the guarded value on the rest of the loop
// body, as TypeScript does. skjs loses the narrowing because `isTerminal()`
// (Termination.sk) counts only `return`/`throw` as terminal, not
// `continue`/`break`. Surfaced by the regenerated generated-examples
// (file-metadata, search-index). See also #87.
// FIXME(#764): skjs should narrow after a continue/break guard; tsc accepts.
export function continueGuardNarrowing(
  xs: Array<string | undefined>,
): string[] {
  const out: string[] = [];
  for (const x of xs) {
    if (x === undefined) continue;
    // @skjs-expect-error Argument is not assignable to the parameter's type
    out.push(x);
  }
  return out;
}
