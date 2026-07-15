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

// A block reached by falling through empty cases runs under the disjunction of
// every label leading into it, so it narrows to their union: reaching this body
// means `x === 1 || x === 2`, not just `x === 2`.
function testGroupNarrowsToUnion(x: 1 | 2): void {
  switch (x) {
    case 1:
    case 2:
      // @skjs-expect-error Type of value is not assignable to the variable's type annotation
      const y: 2 = x;
      break;
  }
}

function testGroupNarrowsToUnionAccepted(x: 1 | 2 | 3): void {
  switch (x) {
    case 1:
    case 2:
      const z: 1 | 2 = x;
      break;
    default:
      break;
  }
}

// A `default` in the group makes the body reachable for any unmatched value,
// which no disjunction of labels describes, so the labels do not narrow it.
function testGroupWithDefaultDoesNotNarrow(x: 1 | 2): void {
  switch (x) {
    case 1:
    default:
      const w: 1 | 2 = x;
      break;
  }
}
