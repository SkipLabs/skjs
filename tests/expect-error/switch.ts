function switchUsePreciseTyping(): void {
  switch (1) {
    case 1:
      return;
    // @skjs-expect-warning This case is unreachable: its value is not in the switched type
    case 2:
      return;
  }
}

function switchUsePreciseTyping2(): void {
  switch (1) {
    case 1:
      return;
    // @skjs-expect-warning This 'default' case is unreachable: all values of the switched type are already handled
    default:
      return;
  }
}

function defaultClauseNotLast(x: number): void {
  // @skjs-expect-warning The 'default' clause should be the last branch of a switch
  switch (x) {
    default:
      return;
    case 1:
      return;
  }
}

// FIXME: a `default` between two cases is not last either, but only a *leading*
// `default` is flagged today. Pinned to the current behavior (no warning);
// fixed in a later commit.
function defaultClauseInTheMiddle(x: number): void {
  switch (x) {
    case 1:
      return;
    default:
      return;
    case 2:
      return;
  }
}

// A `case` following a non-last `default` is still reachable: JS matches a
// `case` by value regardless of `default`'s position (falling to `default` only
// when no `case` matches), so `case 1`/`case 2` must not be flagged unreachable.
// The `default` itself is unreachable here, since the cases cover all of 1 | 2.
function caseAfterDefaultReachable(x: 1 | 2): void {
  // @skjs-expect-warning The 'default' clause should be the last branch of a switch
  switch (x) {
    // @skjs-expect-warning This 'default' case is unreachable: all values of the switched type are already handled
    default:
      return;
    case 1:
      return;
    case 2:
      return;
  }
}
