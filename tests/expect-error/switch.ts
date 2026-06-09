function switchUsePreciseTyping(): void {
  switch (1) {
    case 1:
      return;
    // @skjs-expect-error This case is unreachable: its value is not in the switched type
    case 2:
      return;
  }
}

function switchUsePreciseTyping2(): void {
  switch (1) {
    case 1:
      return;
    // @skjs-expect-error This case is unreachable: its value is not in the switched type
    default:
      return;
  }
}
