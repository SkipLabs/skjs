function doesNotAlwaysReturnAValue(b: boolean): boolean {
  // @ts-expect-error Useless switch
  switch (b) {
    case true:
      return true;
  }
}

function doesNotAlwaysReturnAValue2(i: 1 | 2 | 3): boolean {
  // @ts-expect-error Missing branches
  switch (i) {
    case 1:
      return true;
    case 2:
      return false;
  }
}

// @ts-expect-error This function may not always return a value
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
