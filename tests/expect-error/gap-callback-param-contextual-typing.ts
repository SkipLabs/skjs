// Contextual typing of an un-annotated callback parameter (e.g. the comparator
// of Array.prototype.sort) is not modelled: TypeScript types `x`/`y` from the
// comparator signature, but skjs demands an explicit annotation. Surfaced by
// the regenerated generated-examples (leaderboard, notifications, ...).
// FIXME(#763): skjs should contextually type these params; tsc --strict accepts.
export function contextualSortParams(a: number[]): number[] {
  // @skjs-expect-error A parameter must have an explicit type annotation
  return a.slice().sort((x, y) => x - y);
}
