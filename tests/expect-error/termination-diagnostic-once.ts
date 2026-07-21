// A diagnostic owned by the termination analysis is reported exactly once.
// When a separate walker computed termination, it re-walked each statement
// once per enclosing construct that asked, duplicating the diagnostic per walk
// (SkipLabs/skjs#891: four times in a switch clause, twice at a function's top
// level) — which also made this construct untestable, since the harness
// rightly rejects duplicate annotations and enforces exact counts. Termination
// is an output of checking now, so the walk — and the report — happen once.

function inASwitchClause(x: number, o: { a: number }, arr: number[]): void {
  switch (x) {
    case 1:
      // @skjs-expect-error A for-loop variable initializer must be a plain value, but this one may throw.
      // @skjs-expect-error A loop variable must be a simple 'let' or 'const' binding
      for (o.a of arr) {
      }
      break;
    case 2:
      break;
  }
}

function atFunctionTopLevel(o: { a: number }, arr: number[]): void {
  // @skjs-expect-error A for-loop variable initializer must be a plain value, but this one may throw.
  // @skjs-expect-error A loop variable must be a simple 'let' or 'const' binding
  for (o.a of arr) {
  }
}
