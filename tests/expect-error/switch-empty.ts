// A switch with no clauses evaluates the scrutinee and does nothing else. That
// is sound, and tsc accepts it silently, so it is a lint concern rather than an
// error — pointless code, not wrong code.
//
// It used to crash the checker instead: the termination pass reduced the
// branches to one answer and had none to give over no branches, and it runs
// before the check below ever gets to report anything (SkipLabs/skjs#890). The
// diagnostic was therefore unreachable and untestable until then.
function emptySwitch(x: number): void {
  // @skjs-expect-warning A switch statement must have at least one case
  switch (x) {
  }
}

// Having no clauses says nothing about the scrutinee, which is real code and
// still reports its own errors.
function emptySwitchOverUnknownName(): void {
  // @skjs-expect-error Cannot find name
  // @skjs-expect-warning A switch statement must have at least one case
  switch (nope) {
  }
}

function emptySwitchOverBadProperty(o: { a: number }): void {
  // @skjs-expect-error Property 'nosuch' does not exist on this type
  // @skjs-expect-warning A switch statement must have at least one case
  switch (o.nosuch) {
  }
}
