// Switch statements with empty cases.
//
// Falling *through* means running one clause's statements and then running the
// next clause's too. An empty clause has none to run — it is how several labels
// are given one body — and the last clause has nothing to fall into, so neither
// is a fallthrough.

function testSimpleEmpty(x: number): void {
  switch (x) {
    case 1:
    case 2:
      const y: number = 1;
  }
}

// Every path returns: an empty case falls into the next clause, and both of
// those return.
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

// Chaining an empty clause is what lets a switch count as always returning, so
// a block ending in one is terminal — and what follows an `if` around it keeps
// the else branch's narrowing rather than merging both.
function terminalSwitchNarrowsAfterIf(x: string, n: number | string): void {
  if (typeof n === "string") {
    switch (x) {
      case "a":
      case "b":
        return;
      default:
        return;
    }
  }
  const m: number = n;
}

// A clause that breaks leaves the switch rather than continuing into the next
// one, so grouping labels in front of it does not make the switch return.
// @skjs-expect-error Not all code paths return a value, and the return type does not include 'undefined'
function testGroupedLabelsThatBreak(x: string): number {
  switch (x) {
    case "a":
    case "b":
      break;
    default:
      return 0;
  }
}

// A clause that has statements and falls into a following one is a fallthrough:
// only an empty clause and the last clause are exempt.
function testNonEmptyFallthrough(x: number): void {
  switch (x) {
    case 1:
      // @skjs-expect-error Fallthrough case in switch; add a 'break'
      const y: number = 1;
    case 2:
      break;
  }
}
