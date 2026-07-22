// A `continue` guard narrows the guarded value on the rest of the loop body,
// as TypeScript does: `isTerminalBlock` (TypeCheck.sk) treats a branch as a
// live path out of an `if` only when it may fall through, so a `continue` (or
// `break`) branch — like a `return`/`throw` one — is excluded from the merge
// and the other branch's narrowing survives alone. Surfaced by the
// regenerated generated-examples (file-metadata, search-index). See also #87.
export function continueGuardNarrowing(
  xs: Array<string | undefined>,
): string[] {
  const out: string[] = [];
  for (const x of xs) {
    if (x === undefined) continue;
    // Pins today's behaviour: the continue branch is merged back, so `x` stays
    // possibly-undefined. The next commit drops the branch and narrows.
    // @skjs-expect-error Argument is not assignable to the parameter's type
    out.push(x);
  }
  return out;
}
