// Loose equality (`==` / `!=`) is a lint concern (ESLint `eqeqeq`), not a
// soundness error: SKJS reports each occurrence as a warning and otherwise
// parses and type-checks it normally — the result is `boolean`, and no
// narrowing follows from it (unlike `===`, whose refinement is strict).
// Coercion also means disjoint-looking operand types can still compare equal
// at runtime (`0 == ""`, `null == undefined`), so no "always false" overlap
// diagnostic is emitted for `==`/`!=`.

function eqWarns(x: number, y: number): boolean {
  // @skjs-expect-warning Unexpected '=='; use '===' instead (loose equality coerces its operands)
  return x == y;
}

function neWarns(x: number, y: number): boolean {
  // @skjs-expect-warning Unexpected '!='; use '!==' instead (loose inequality coerces its operands)
  return x != y;
}

// Usable as a condition; the branches narrow nothing.
function noNarrowing(x: string | number, y: string | number): void {
  // @skjs-expect-warning Unexpected '=='; use '===' instead (loose equality coerces its operands)
  if (x == y) {
    // `x` is NOT narrowed to `y`'s type here (with `===` it could be): `1 == "1"`
    // is true at runtime, so `x` may still be the number when `y` is `"1"`.
    // @skjs-expect-error Type of value is not assignable to the variable's type annotation
    const n: number = x;
  }
}

// No overlap diagnostic for disjoint types: `0 == ""` is true at runtime.
function disjointTypesStillWarnOnlyEqeqeq(x: number, y: string): boolean {
  // @skjs-expect-warning Unexpected '=='; use '===' instead (loose equality coerces its operands)
  return x == y;
}

// `null == undefined` is true at runtime; only the eqeqeq warning fires.
function nullVsUndefined(x: null, y: undefined): boolean {
  // @skjs-expect-warning Unexpected '=='; use '===' instead (loose equality coerces its operands)
  return x == y;
}

// Left-associative, like the strict variants: `a == b == c` is `(a == b) == c`
// (a boolean compared to `c`), and each `==` warns once.
function chained(a: boolean, b: number, c: number): void {
  // @skjs-expect-warning Unexpected '=='; use '===' instead (loose equality coerces its operands)
  const r1: boolean = a == b;
  // @skjs-expect-warning Unexpected '=='; use '===' instead (loose equality coerces its operands)
  const r2: boolean = r1 == c;
}

// Works in any expression position.
function inPositions(x: number, y: number): void {
  // @skjs-expect-warning Unexpected '=='; use '===' instead (loose equality coerces its operands)
  const b: boolean = x == y ? true : false;
  // @skjs-expect-warning Unexpected '!='; use '!==' instead (loose inequality coerces its operands)
  while (x != y) {
    break;
  }
}

// Comparison against a literal still warns (the eqeqeq rule has no literal
// exemption — that exemption belongs to the always-true/false `===` lint).
function againstLiteral(x: number): boolean {
  // @skjs-expect-warning Unexpected '=='; use '===' instead (loose equality coerces its operands)
  return x == 1;
}
