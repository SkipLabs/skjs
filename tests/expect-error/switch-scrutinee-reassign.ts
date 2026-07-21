// When a clause reassigns the scrutinee variable and falls through, the clause
// it falls into is reached with that reassigned value, not the label that was
// matched at entry. So the scrutinee there is the union, over the ways the body
// is reached, of the scrutinee's value on each: the label on a direct entry,
// and whatever a falling clause left it at on a fallthrough entry.

// Reaching `case "b"` directly means `y` is "b"; reaching it by falling through
// `case "a"` (which set `y = c`) means `y` is "c". So `y` is "b" | "c" here, and
// returning it from a function typed "a" | "b" must be rejected: at runtime
// `scr("a", "c")` returns "c".
function reassignedScrutineeCarriesAcross(
  y: "a" | "b" | "c",
  c: "c",
): "a" | "b" {
  switch (y) {
    case "a":
      // @skjs-expect-error Fallthrough case in switch; add a 'break'
      y = c;
    case "b":
      // Pins today's behaviour, which is unsound: `y` is narrowed to the entry
      // label "b", dropping the "c" the fallthrough carried, so this is wrongly
      // accepted. The next commit rejects it.
      return y;
    default:
      return "a";
  }
}

// The mirror case: reassigning the scrutinee to a value the fallen-into label
// also allows leaves it exactly that. `y` is "b" on the direct entry and "b" on
// the fallthrough (which set `y = b`), so `y` is "b" here — narrower than the
// "a" | "b" the entry labels would suggest.
function reassignedIntoLabelIsExact(y: "a" | "b", b: "b"): void {
  switch (y) {
    case "a":
      // @skjs-expect-error Fallthrough case in switch; add a 'break'
      y = b;
    case "b":
      // @skjs-expect-error Type of value is not assignable to the variable's type annotation
      const z: "b" = y;
      break;
  }
}

// The union is exactly the direct-entry label and the carried value — neither
// dropping the carried "c" (unsound) nor keeping the entry label "a" that no
// path reaches here with (over-wide). `y` is "b" | "c".
function unionOfLabelAndCarried(y: "a" | "b" | "c", c: "c"): void {
  switch (y) {
    case "a":
      // @skjs-expect-error Fallthrough case in switch; add a 'break'
      y = c;
    case "b":
      // @skjs-expect-error Type of value is not assignable to the variable's type annotation
      const z: "b" | "c" = y;
      break;
    default:
      break;
  }
}
