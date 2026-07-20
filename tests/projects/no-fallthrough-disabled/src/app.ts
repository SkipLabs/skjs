// With `noFallthroughCasesInSwitch: false`, a clause that falls into another is
// not reported. What the fallthrough means is unchanged: the clause fallen into
// is still reached by the labels of everything that falls into it, and is
// narrowed to their union.

export function deliberateFallthrough(
  x: 1 | 2,
  log: (s: string) => void,
): void {
  switch (x) {
    case 1:
      log("one, and then two");
    case 2:
      log("two");
      break;
  }
}

// Reaching this body means `x` is `1` or `2`, not `2` alone — the fallthrough
// being allowed does not make it safe to assume the label matched.
export function narrowingSurvives(x: 1 | 2, log: (s: string) => void): void {
  switch (x) {
    case 1:
      log("one");
    case 2:
      // @skjs-expect-error Type of value is not assignable to the variable's type annotation
      const y: 2 = x;
      break;
  }
}

export function unionIsAccepted(x: 1 | 2, log: (s: string) => void): void {
  switch (x) {
    case 1:
      log("one");
    case 2:
      const y: 1 | 2 = x;
      break;
  }
}

// Allowing the fallthrough does not change what it does: `case 1`'s write is in
// effect in the body it falls into, where `y` is `"b"` and not the `"a"` the
// switch was entered with. Pins today's behaviour, which is unsound — and
// silently so here, with no fallthrough diagnostic to hint at it.
export function fallthroughCarriesItsWrites(x: 1 | 2, a: "a", b: "b"): void {
  let y: "a" | "b" = a;
  y = a;
  switch (x) {
    case 1:
      y = b;
    case 2:
      const y2: "a" = y;
      break;
  }
}
