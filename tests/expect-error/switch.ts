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

// FIXME: a `case` following a non-last `default` is wrongly flagged
// unreachable. JS matches a `case` by value regardless of `default`'s position
// (falling to `default` only when no `case` matches), so `case 1`/`case 2` are
// reachable; only the `default` is unreachable here, since the cases cover all
// of 1 | 2. Pinned to the current (incorrect) behavior; fixed in the next commit.
function caseAfterDefaultReachable(x: 1 | 2): void {
  // @skjs-expect-warning The 'default' clause should be the last branch of a switch
  switch (x) {
    default:
      return;
    // @skjs-expect-warning This case is unreachable: its value is not in the switched type
    case 1:
      return;
    // @skjs-expect-warning This case is unreachable: its value is not in the switched type
    case 2:
      return;
  }
}
