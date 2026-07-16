// A switch with no clauses parses fine but runs nothing, so SKJS rejects it.
//
// This used to crash the checker instead: the termination pass folded the
// branches with an `or` that has no answer over an empty sequence, and it runs
// before the check below ever gets to report anything (SkipLabs/skjs#890). The
// diagnostic was therefore unreachable and untestable until now.
function emptySwitch(x: number): void {
  // @skjs-expect-error A switch statement must have at least one case
  switch (x) {
  }
}
