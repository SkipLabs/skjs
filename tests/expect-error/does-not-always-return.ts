// @skjs-expect-error Not all code paths return a value, and the return type does not include 'undefined'
function doesNotAlwaysReturnAValue(b: boolean): boolean {
  // @skjs-expect-warning This switch has a single branch; use an 'if' statement instead
  switch (b) {
    case true:
      return true;
  }
}

// @skjs-expect-error Not all code paths return a value, and the return type does not include 'undefined'
function doesNotAlwaysReturnAValue2(i: 1 | 2 | 3): boolean {
  // @skjs-expect-error Switch is not exhaustive; the following cases are unhandled
  switch (i) {
    case 1:
      return true;
    case 2:
      return false;
  }
}

// @skjs-expect-error Not all code paths return a value, and the return type does not include 'undefined'
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
