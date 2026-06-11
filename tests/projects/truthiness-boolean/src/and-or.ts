// In `boolean` mode the operator must produce a boolean, so BOTH operands of
// `&&`/`||` are required to be boolean (unlike the relaxed/javascript modes,
// where `&&`/`||` are value-returning and the right operand flows through
// unchecked). tsc accepts a non-boolean operand here, so these rejections are
// SKJS-only.

// Both operands boolean: accepted, result is boolean.
function boolAnd(x: boolean, y: boolean): boolean {
  return x && y;
}

function boolOr(x: boolean, y: boolean): boolean {
  return x || y;
}

// Non-boolean right operand is rejected too — `boolean` mode checks the right
// operand, not just the left.
function rejectAndRhs(b: boolean): number | boolean {
  // @skjs-expect-error Operand of '&&' must be of type 'boolean'
  return b && 5;
}

function rejectOrRhs(b: boolean): number | boolean {
  // @skjs-expect-error Operand of '||' must be of type 'boolean'
  return b || 5;
}
