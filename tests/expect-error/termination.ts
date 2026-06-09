// @skjs-expect-error Not all code paths return a value, and the return type does not include 'undefined'
function breaksInSwitch(b: boolean): number {
  switch (b) {
    case true:
      break;
    default:
      break;
  }
}

// @skjs-expect-error Not all code paths return a value, and the return type does not include 'undefined'
function breakInLoop(): number {
  while (true) {
    break;
  }
}
