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
  // @skjs-expect-error The 'default' clause must be the last branch of a switch
  switch (x) {
    default:
      return;
    case 1:
      return;
  }
}
