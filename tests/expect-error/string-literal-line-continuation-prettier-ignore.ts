// prettier-ignore
// A LineContinuation (backslash + line terminator) has ECMAScript string value
// "" (empty), which is falsy (issue #771). So a union of a line-continuation
// string literal type with 0 has two falsy members, exactly like the canonical
// "" | 0 control below: `if (x)` is rejected (two falsy values, not one), and
// the else branch runs at x = "" so `const z: 0 = x` is a type error.
//
// Pinned to the buggy pre-fix behavior: the line-continuation lexeme was stored
// undecoded (non-empty, hence wrongly truthy), so `if (x)` was accepted and the
// else branch narrowed to 0. The fix makes it behave like the "" | 0 control.

function lineContinuationIsFalsy(x: "\
" | 0): void {
  if (x) {
  } else {
    const z: 0 = x;
  }
}

// Canonical control: an explicit empty-string member is already handled and
// stays rejected before and after the fix.
function emptyStringControl(x: "" | 0): void {
  // @skjs-expect-error A condition is expected to be of type boolean or a type with a single falsy value
  if (x) {
  } else {
    // @skjs-expect-error Type of value is not assignable to the variable's type annotation
    const z: 0 = x;
  }
}
