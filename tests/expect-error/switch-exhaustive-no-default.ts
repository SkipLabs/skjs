// A switch whose cases leave no value unmatched always runs one of them, just as
// one with a `default` does — so it neither escapes to the code after it nor
// leaves a binding at its pre-switch value.

// Every value of `1 | 2` is handled and every clause returns, so this returns on
// every path.
function exhaustiveWithoutDefault(x: 1 | 2): boolean {
  switch (x) {
    case 1:
      return true;
    case 2:
      return false;
  }
}

// `y` is assigned by every clause that can be taken, so it is never left at "a"
// here.
function exhaustiveLeavesNoBindingUntouched(
  x: 1 | 2,
  a: "a",
  b: "b",
  c: "c",
): void {
  let y: "a" | "b" | "c" = a;
  switch (x) {
    case 1:
      y = b;
      break;
    case 2:
      y = c;
      break;
  }
  const z: "b" | "c" = y;
}

// A case left unhandled is a value that reaches neither clause.
// @skjs-expect-error Not all code paths return a value, and the return type does not include 'undefined'
function missingACase(x: 1 | 2 | 3): boolean {
  // @skjs-expect-warning Switch is not exhaustive; the following cases are unhandled
  switch (x) {
    case 1:
      return true;
    case 2:
      return false;
  }
}

// Nothing is known to be covered when the scrutinee's values cannot be listed.
// @skjs-expect-error Not all code paths return a value, and the return type does not include 'undefined'
function nonLiteralScrutinee(x: number): boolean {
  switch (x) {
    case 1:
      return true;
    case 2:
      return false;
  }
}

// Covering every value is not enough if a clause escapes rather than returns.
// @skjs-expect-error Not all code paths return a value, and the return type does not include 'undefined'
function exhaustiveButAClauseBreaks(x: 1 | 2): boolean {
  switch (x) {
    case 1:
      break;
    case 2:
      return false;
  }
}

// Repeating a case covers its value once, not the one it left out.
// @skjs-expect-error Not all code paths return a value, and the return type does not include 'undefined'
function repeatedCase(x: 1 | 2): boolean {
  // @skjs-expect-warning Switch is not exhaustive; the following cases are unhandled
  switch (x) {
    case 1:
      return true;
    // @skjs-expect-warning This case is unreachable: its value is already handled by an earlier case
    case 1:
      return false;
  }
}
