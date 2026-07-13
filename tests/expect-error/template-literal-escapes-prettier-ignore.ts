// prettier-ignore
// Template literals decode escape sequences like quoted strings (#810), so a
// simple (non-interpolated) template denotes the decoded string. Template
// literal *types* are unsupported, so there is no value/type asymmetry.
// Pinned to the pre-fix behavior, where template values kept their raw
// lexeme; the fix removes the annotations on the equivalence cases.

function templateHexEscape(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const a: "a" = `\x61`;
}

function templateNamedEscape(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const a: "\n" = `\n`;
}

function templateCodePointEscape(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const a: "a" = `\u{61}`;
}

// Negative control: a genuinely different value stays a type error.
function templateMismatchControl(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const a: "a" = `\x62`;
}
