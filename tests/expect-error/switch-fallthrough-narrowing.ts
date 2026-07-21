// A case body runs only when the scrutinee equals that case's value, so the
// scrutinee is narrowed to it inside the body. When empty clauses fall into a
// body, it runs whenever any of their labels matches, so it must be narrowed to
// their union — not just its own label.

// Reaching this body means `x === 1 || x === 2`, so `x` is `1 | 2` here, not
// `2`: this would return `1` from a function typed `2` when called with `1`.
function narrowsToUnionNotLastLabel(x: 1 | 2): 2 {
  switch (x) {
    case 1:
    case 2:
      // @skjs-expect-error Type of returned value is not assignable to the function's return type
      return x;
  }
  return 2;
}

// An empty `default` before a case makes that case's body reachable for any
// unmatched value too (the body runs for `x === 2` by falling through
// `default`), so `x` is not narrowed to `1` here.
function emptyDefaultFirstDoesNotNarrow(x: 1 | 2): void {
  switch (x) {
    // @skjs-expect-warning The 'default' clause should be the last branch of a switch
    default:
    case 1:
      // @skjs-expect-error Type of value is not assignable to the variable's type annotation
      const y: 1 = x;
      break;
  }
}

// The body is correctly narrowed to the union, so assigning it to that union is
// accepted.
function narrowsToUnionAccepted(x: 1 | 2 | 3): void {
  switch (x) {
    case 1:
    case 2:
      const y: 1 | 2 = x;
      break;
    default:
      break;
  }
}

// A single (non-grouped) case narrows the scrutinee to its own label.
function singleLabelNarrows(x: 1 | 2): void {
  switch (x) {
    case 1:
      const y: 1 = x;
      break;
    case 2:
      break;
  }
}

// A `default` body is reachable for any unmatched value, so it is not narrowed
// to a preceding case's label.
function defaultDoesNotNarrowToCaseLabel(x: 1 | 2): void {
  switch (x) {
    case 1:
      break;
    default:
      // @skjs-expect-error Type of value is not assignable to the variable's type annotation
      const y: 1 = x;
      break;
  }
}

// A clause with statements falls into the next one just as an empty one does,
// so this body is reached when `x` is `1` too and is not `2` alone. (The
// fallthrough is also reported, since this switch does not turn that off.)
function nonEmptyClauseFallsThrough(x: 1 | 2, log: (s: string) => void): void {
  switch (x) {
    case 1:
      // @skjs-expect-error Fallthrough case in switch; add a 'break'
      log("one");
    case 2:
      // @skjs-expect-error Type of value is not assignable to the variable's type annotation
      const y: 2 = x;
      break;
  }
}

// A clause falls into the next by running its own statements first, so a write
// it makes is already in effect in the clause fallen into: reaching this body
// through `case 1` leaves `y` at `"b"`, not at the `"a"` the switch was entered
// with.
function fallthroughCarriesItsWrites(x: 1 | 2, a: "a", b: "b"): void {
  let y: "a" | "b" = a;
  y = a;
  switch (x) {
    case 1:
      // @skjs-expect-error Fallthrough case in switch; add a 'break'
      y = b;
    case 2:
      // @skjs-expect-error Type of value is not assignable to the variable's type annotation
      const y2: "a" = y;
      break;
  }
}

// Both entries are possible, so the body sees the union of what they leave
// behind: `case 1`'s write, or the value the switch was entered with.
function fallthroughWriteIsUnioned(x: 1 | 2, a: "a", b: "b"): void {
  let y: "a" | "b" = a;
  y = a;
  switch (x) {
    case 1:
      // @skjs-expect-error Fallthrough case in switch; add a 'break'
      y = b;
    case 2:
      const y3: "a" | "b" = y;
      break;
  }
}

// A clause that breaks does not fall into the next, so its write is not in
// effect there: this body is reached only by matching its own label, with `y`
// still at the `"a"` the switch was entered with.
function breakingClauseDoesNotCarry(x: 1 | 2 | 3, a: "a", b: "b"): void {
  let y: "a" | "b" = a;
  y = a;
  switch (x) {
    case 1:
      y = b;
      break;
    case 2:
      const y4: "a" = y;
      break;
    case 3:
      break;
  }
}

// Only the clause fallen *into* is reached with the write in effect; a later
// clause reached on its own label is not, so the write does not widen it.
function laterClauseDoesNotSeeTheWrite(
  x: 1 | 2 | 3,
  a: "a",
  b: "b",
  log: (s: string) => void,
): void {
  let y: "a" | "b" = a;
  y = a;
  switch (x) {
    case 1:
      // @skjs-expect-error Fallthrough case in switch; add a 'break'
      y = b;
    case 2:
      log("two");
      break;
    case 3:
      const y5: "a" = y;
      break;
  }
}
