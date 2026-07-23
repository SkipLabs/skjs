// A `++`/`--` on a plain variable writes it back: the binding holds `number`
// afterwards, not whatever it was narrowed to. Reading it as the pre-increment
// narrowed type must be caught, straight-line, with no control flow needed
// (SkipLabs/skjs#1017).

// `y` is narrowed to `0`, then `y++` makes it `1` — reading it as `0` is unsound.
function incrementClearsNarrowing(): void {
  let y: number = 0;
  if (y !== 0) return; // y narrowed to 0
  y++;
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const z: 0 = y;
}

// `--` writes the binding back just the same.
function decrementClearsNarrowing(): void {
  let y: number = 0;
  if (y !== 0) return;
  y--;
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const z: 0 = y;
}

// After the write the binding is plain `number`, which reads back fine — the
// write-back must not spuriously reject a widened read.
function incrementWidensToNumber(): void {
  let y: number = 0;
  if (y !== 0) return;
  y++;
  const z: number = y;
}

// A `++` on a member target is unaffected: there is no narrowed binding to
// clear, and the field keeps its declared `number` type.
function incrementMemberIsFine(o: { n: number }): void {
  o.n++;
  const z: number = o.n;
}
