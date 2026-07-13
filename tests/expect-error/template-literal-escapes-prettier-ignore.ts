// prettier-ignore
// Template literals decode escape sequences like quoted strings (#810), so a
// simple (non-interpolated) template denotes the decoded string. Template
// literal *types* are unsupported, so there is no value/type asymmetry.

function templateHexEscape(): void {
  const a: "a" = `\x61`;
}

function templateNamedEscape(): void {
  const a: "\n" = `\n`;
}

function templateCodePointEscape(): void {
  const a: "a" = `\u{61}`;
}

// Negative control: a genuinely different value stays a type error.
function templateMismatchControl(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const a: "a" = `\x62`;
}
