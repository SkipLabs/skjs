// @ts-expect-error This function may not always return a value
function breaksInSwitch(b: boolean): number {
  switch (b) {
    case true:
      break;
    default:
      break;
  }
}

// @ts-expect-error This function may not always return a value
function breakInLoop(): number {
  while (true) {
    break;
  }
}
