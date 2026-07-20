// A `default` runs only for a value that no `case` matched, so its body can be
// narrowed by that: the scrutinee is the switched type minus every case label.

// Reaching this body means `x` is neither 1 nor 2, so it is `3`.
function defaultIsTheComplement(x: 1 | 2 | 3): void {
  switch (x) {
    case 1:
      break;
    case 2:
      break;
    default:
      const y: 3 = x;
      break;
  }
}

// Same with one case ruled out — `x` is `2 | 3` here.
function defaultRulesOutOneCase(x: 1 | 2 | 3): void {
  switch (x) {
    case 1:
      break;
    default:
      const y: 2 | 3 = x;
      break;
  }
}

// Ruling out a case must not rule out more than it: `x` is still `2 | 3` here,
// so narrowing it to `3` stays wrong.
function defaultDoesNotOverNarrow(x: 1 | 2 | 3): void {
  switch (x) {
    case 1:
      break;
    default:
      // @skjs-expect-error Type of value is not assignable to the variable's type annotation
      const y: 3 = x;
      break;
  }
}

// An empty case falling into the `default` makes its body reachable for that
// case's value too, so it is not the complement any more.
function emptyCaseFallingIntoDefault(x: 1 | 2): void {
  switch (x) {
    case 1:
    default:
      // @skjs-expect-error Type of value is not assignable to the variable's type annotation
      const y: 2 = x;
      break;
  }
}

// With no case to rule out, the `default` runs whatever the scrutinee is.
function defaultWithNoCases(x: 1 | 2): void {
  // @skjs-expect-warning This switch has a single branch; use an 'if' statement instead
  switch (x) {
    default:
      const y: 1 | 2 = x;
      break;
  }
}

// A scrutinee with no enumerable values has nothing to subtract from.
function defaultOverNonLiteral(x: string): void {
  switch (x) {
    case "a":
      break;
    default:
      const y: string = x;
      break;
  }
}

// FIXME: where the clauses sit says nothing about which values reach the
// `default`, so a case written after it rules its value out just as much. Cases
// after the `default` are currently not ruled out. Pinned to the current
// (imprecise) behavior; fixed in the next commit.
function defaultBeforeItsCases(x: 1 | 2 | 3): void {
  switch (x) {
    // @skjs-expect-warning The 'default' clause should be the last branch of a switch
    default:
      // @skjs-expect-error Type of value is not assignable to the variable's type annotation
      const y: 3 = x;
      break;
    case 1:
      break;
    case 2:
      break;
  }
}
