// Number and bigint literals keep the user-written spelling for diagnostics:
// the literal's TYPE stays the canonical value (rule 30: 0xf IS 15), but
// errors and __SKJS_show print what the user wrote ("0xf", not "15").

// --- number literal in a type annotation ---

function hexTypeOk(): void {
  const ok: 0xf = 15;
  __SKJS_show(ok, "0xf");
}
function hexTypeBad(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  // @skjs-expect-error-line2 Type '16'
  // @skjs-expect-error-line3 is not assignable to type '0xf'
  const bad: 0xf = 16;
}

// --- bigint literal in a type annotation ---

function bigHexOk(): void {
  const ok: 0x10n = 16n;
  __SKJS_show(ok, "0x10n");
}
function bigHexBad(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  // @skjs-expect-error-line2 Type '17n'
  // @skjs-expect-error-line3 is not assignable to type '0x10n'
  const bad: 0x10n = 17n;
}

// --- enum member initializer ---

enum HexEnum {
  A = 0xff,
}
function enumValBad(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  // @skjs-expect-error-line3 is not assignable to type '0xff'
  const e: HexEnum = 256;
}

// --- expression literal, narrowed by === ---

function exprNarrow(x: number): void {
  if (x === 0x10) {
    __SKJS_show(x, "0x10");
  }
}

// --- other spellings of the same value ---

function sepOk(): void {
  const s: 1_000 = 1000;
  __SKJS_show(s, "1_000");
}
function expOk(): void {
  const e: 1e3 = 1000;
  __SKJS_show(e, "1e3");
}
function negOk(): void {
  const n: -0x10 = -16;
  __SKJS_show(n, "-0x10");
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
