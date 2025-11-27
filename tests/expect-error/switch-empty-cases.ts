// Test switch statements with empty cases

function testSimpleEmpty(x: number): void {
  switch (x) {
    // @skjs-expect-error Missing break
    case 1:
    case 2:
      const y: number = 1;
  }
}

function testEmptyCases(x: number): string {
  switch (x) {
    // @skjs-expect-error Missing break
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
    // @skjs-expect-error Missing break
    case 1:
    case 2:
    case 3:
    default:
  }
}

function testMixedCases(x: string): number {
  switch (x) {
    case "a":
      return 1;
    // @skjs-expect-error Missing break
    case "b":
    // Empty
    case "c":
      return 2;
    default:
      return 0;
  }
}
