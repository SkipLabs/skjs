// Test that empty statements (;) after if are reported as warnings (the
// `no-empty` lint rule), not errors: `if (x);` is runtime-sound, it just runs
// nothing when the condition holds.

function testEmptyIfStmt(): void {
  const x: number = 5;

  // @skjs-expect-warning The body of an 'if' statement cannot be the empty statement
  if (x > 0);
}

// A warning never aborts checking of the definition: an error after the
// empty-`if` warning is still reported.
function testEmptyIfStmtThenError(): void {
  const x: number = 5;

  // @skjs-expect-warning The body of an 'if' statement cannot be the empty statement
  if (x > 0);
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const s: string = x;
}
