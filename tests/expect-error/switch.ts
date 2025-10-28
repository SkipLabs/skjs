function switchUsePreciseTyping(): void {
  switch (1) {
    case 1:
      return;
    // @ts-expect-error Unused branch
    case 2:
      return;
  }
}

function switchUsePreciseTyping2(): void {
  switch (1) {
    case 1:
      return;
    // @skjs-expect-error Unused branch
    default:
      return;
  }
}
