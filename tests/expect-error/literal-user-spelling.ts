// Default behavior (TsCompilerOptions.userLiteralSpelling off, the default):
// number and bigint literals print their CANONICAL value in diagnostics
// (rule 30: 0xf prints as 15), even though the literal's type is the same.
// The flag-on behavior (user-written spellings) is tested in
// tests/projects/user-literal-spelling/.

// --- number literal in a type annotation ---

function hexTypeOk(): void {
  const ok: 0xf = 15;
  __SKJS_show(ok, "15");
}
function hexTypeBad(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  // @skjs-expect-error-line2 Type '16'
  // @skjs-expect-error-line3 is not assignable to type '15'
  const bad: 0xf = 16;
}

// --- bigint literal in a type annotation ---

function bigHexOk(): void {
  const ok: 0x10n = 16n;
  __SKJS_show(ok, "16n");
}
function bigHexBad(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  // @skjs-expect-error-line2 Type '17n'
  // @skjs-expect-error-line3 is not assignable to type '16n'
  const bad: 0x10n = 17n;
}

// --- enum member initializer ---

enum HexEnum {
  A = 0xff,
}
function enumValBad(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  // @skjs-expect-error-line3 is not assignable to type '255'
  const e: HexEnum = 256;
}

// --- expression literal, narrowed by === ---

function exprNarrow(x: number): void {
  if (x === 0x10) {
    __SKJS_show(x, "16");
  }
}

// --- other spellings of the same value ---

function sepOk(): void {
  const s: 1_000 = 1000;
  __SKJS_show(s, "1000");
}
function expOk(): void {
  const e: 1e3 = 1000;
  __SKJS_show(e, "1000");
}
function negOk(): void {
  const n: -0x10 = -16;
  __SKJS_show(n, "-16");
}

// --- control: strings and booleans print their value, unchanged ---

function strOk(): void {
  const s: "a" = "a";
  __SKJS_show(s, '"a"');
}
function boolOk(): void {
  const b: true = true;
  __SKJS_show(b, "true");
}
