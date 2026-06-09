// @skjs-expect-error This function may not always return a value
function doesNotAlwaysReturnAValue(b: boolean): boolean {
  // @skjs-expect-warning This switch has a single branch; use an 'if' statement instead
  switch (b) {
    case true:
      return true;
  }
}

// @skjs-expect-error This function may not always return a value
function doesNotAlwaysReturnAValue2(i: 1 | 2 | 3): boolean {
  // @skjs-expect-error Switch is not exhaustive; the following cases are unhandled
  switch (i) {
    case 1:
      return true;
    case 2:
      return false;
  }
}

// @skjs-expect-error This function may not always return a value
function doesNotAlwaysReturnAValue3(i: 1 | 2 | 3): boolean {
  switch (i) {
    case 1:
      return true;
    case 2:
      return false;
    default:
      console.log("nah");
  }
}
