// Test switch statements with empty cases.
//
// An empty case is the idiomatic way to group labels (`case 1: case 2:`), and
// the last clause falls out of the switch rather than into another clause, so
// neither is a fallthrough error — matching tsc's `noFallthroughCasesInSwitch`.

function testSimpleEmpty(x: number): void {
  switch (x) {
    case 1:
    case 2:
      const y: number = 1;
  }
}

// @skjs-expect-error Not all code paths return a value, and the return type does not include 'undefined'
function testEmptyCases(x: number): string {
  switch (x) {
    case 1:
    // Empty case - falls through
    case 2:
      return "one or two";
    case 3:
    // Empty case
    default:
      return "other";
  }
}

function testAllEmptyCases(x: number): void {
  switch (x) {
    case 1:
    case 2:
    case 3:
    default:
  }
}

// @skjs-expect-error Not all code paths return a value, and the return type does not include 'undefined'
function testMixedCases(x: string): number {
  switch (x) {
    case "a":
      return 1;
    case "b":
    // Empty
    case "c":
      return 2;
    default:
      return 0;
  }
}

// A case with statements that falls into a following clause is a fallthrough
// error: only an empty case (label grouping) and the last clause are exempt.
function testNonEmptyFallthrough(x: number): void {
  switch (x) {
    case 1:
      // @skjs-expect-error Fallthrough case in switch; add a 'break'
      const y: number = 1;
    case 2:
      break;
  }
}
