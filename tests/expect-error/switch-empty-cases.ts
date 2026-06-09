// Test switch statements with empty cases

function testSimpleEmpty(x: number): void {
  switch (x) {
    // @skjs-expect-error Fallthrough case in switch; add a 'break'
    case 1:
    case 2:
      // @skjs-expect-error Fallthrough case in switch; add a 'break'
      const y: number = 1;
  }
}

// @skjs-expect-error This function may not always return a value
function testEmptyCases(x: number): string {
  switch (x) {
    // @skjs-expect-error Fallthrough case in switch; add a 'break'
    case 1:
    // Empty case - falls through
    case 2:
      return "one or two";
    // @skjs-expect-error Fallthrough case in switch; add a 'break'
    case 3:
    // Empty case
    default:
      return "other";
  }
}

function testAllEmptyCases(x: number): void {
  switch (x) {
    // @skjs-expect-error Fallthrough case in switch; add a 'break'
    case 1:
    // @skjs-expect-error Fallthrough case in switch; add a 'break'
    case 2:
    // @skjs-expect-error Fallthrough case in switch; add a 'break'
    case 3:
    default:
  }
}

// @skjs-expect-error This function may not always return a value
function testMixedCases(x: string): number {
  switch (x) {
    case "a":
      return 1;
    // @skjs-expect-error Fallthrough case in switch; add a 'break'
    case "b":
    // Empty
    case "c":
      return 2;
    default:
      return 0;
  }
}
