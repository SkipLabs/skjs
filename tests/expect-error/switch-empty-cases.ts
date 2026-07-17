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

// Every path returns: an empty case falls into the next clause, and both of
// those return.
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

// A clause that breaks leaves the switch rather than continuing into the next
// one, so grouping labels in front of it does not make the switch return.
// @skjs-expect-error Not all code paths return a value, and the return type does not include 'undefined'
function testGroupedLabelsThatBreak(x: string): number {
  switch (x) {
    // @skjs-expect-error Fallthrough case in switch; add a 'break'
    case "a":
    case "b":
      break;
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
