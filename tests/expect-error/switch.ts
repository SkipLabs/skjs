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
  switch (x) {
    // @skjs-expect-warning The 'default' clause should be the last branch of a switch
    default:
      return;
    case 1:
      return;
  }
}

// A `default` between two cases is not last either, so it is flagged just like
// a leading one.
function defaultClauseInTheMiddle(x: number): void {
  switch (x) {
    case 1:
      return;
    // @skjs-expect-warning The 'default' clause should be the last branch of a switch
    default:
      return;
    case 2:
      return;
  }
}

// A case body runs only when the scrutinee equals that case's value, so the
// scrutinee is narrowed to it inside the body: reaching `case 1` means `x` is
// `1`, and the `default` body is not narrowed at all.
function caseNarrowsTheScrutinee(x: 1 | 2): void {
  switch (x) {
    case 1:
      const one: 1 = x;
      break;
    case 2:
      const two: 2 = x;
      break;
  }
}

function defaultDoesNotNarrowTheScrutinee(x: 1 | 2): void {
  switch (x) {
    case 1:
      break;
    default:
      const both: 1 | 2 = x;
      break;
  }
}

// A `case` following a non-last `default` is still reachable: JS matches a
// `case` by value regardless of `default`'s position (falling to `default` only
// when no `case` matches), so `case 1`/`case 2` must not be flagged unreachable.
// The `default` itself is unreachable here, since the cases cover all of 1 | 2.
function caseAfterDefaultReachable(x: 1 | 2): void {
  switch (x) {
    // @skjs-expect-warning This 'default' case is unreachable: all values of the switched type are already handled
    // @skjs-expect-warning The 'default' clause should be the last branch of a switch
    default:
      return;
    case 1:
      return;
    case 2:
      return;
  }
}
