// Template literal types that denote an infinite but PARTIAL set of strings
// (patterns), issue #897: a whole-primitive hole (`string`, `number`,
// `bigint`) surrounded by text of its own, as in `#${string}` or
// `${number}px`. SKJS keeps such a type as a pattern inside the string
// primitive's domain, and literal-vs-pattern assignability follows tsc's
// greedy-leftmost matcher exactly (see the `${string}-${number}` cases).
//
// SKJS reports only one error per definition, so each rejected assignment
// gets its own function.

// --- String hole with surrounding text ---

type Hex = `#${string}`;
function hex(): void {
  const ok: Hex = "#ff";
  const hash: Hex = "#";
}
function hexNoHash(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const bad: Hex = "ff";
}
function hexEmpty(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const bad: Hex = "";
}

// A pattern is a subtype of `string`, and `string` is not a subtype of it.
function hexVsString(h: Hex, s: string): void {
  const widened: string = h;
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const narrowed: Hex = s;
}

// --- Number hole (`${number}` accepts s iff s != "" && isFinite(+s)) ---

type Px = `${number}px`;
function px(): void {
  const dec: Px = "5px";
  const ws: Px = " 1px";
  const hex: Px = "0x10px";
  const neg: Px = "-5px";
  const plus: Px = "+5px";
  const exp: Px = "1e3px";
}
function pxNoNum(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const bad: Px = "px";
}
function pxSeparator(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const bad: Px = "1_000px";
}
function pxInf(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const bad: Px = "Infinitypx";
}
function pxNan(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const bad: Px = "NaNpx";
}
function pxNoSuffix(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const bad: Px = "5";
}

// --- Bigint hole (`s + "n"` must scan as one BigInt literal) ---

type Big = `${bigint}n`;
function big(): void {
  const dec: Big = "5n";
  const hex: Big = "0xFn";
  const neg: Big = "-5n";
  const bin: Big = "0b101n";
}
function bigPlus(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const bad: Big = "+5n";
}
function bigLeadingZero(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const bad: Big = "05n";
}
function bigSeparator(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const bad: Big = "1_0n";
}
function bigFrac(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const bad: Big = "1.5n";
}

// --- Greedy-leftmost matching, no backtracking ---

type Greedy = `${string}-${number}`;
function greedy(): void {
  const ok: Greedy = "a-1";
}
function greedyNoBacktrack(): void {
  // "a-b-1" IS in the language, but tsc's greedy matcher rejects it, and so do we.
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const bad: Greedy = "a-b-1";
}

// --- Several holes in one template ---

type Both = `a${string}b${number}c`;
function both(): void {
  const ok: Both = "aXb5c";
}
function bothBad(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const bad: Both = "aXbc";
}

// --- A hole mixing a whole primitive with finite literals ---

type Mixed = `${number | "auto"}px`;
function mixed(): void {
  const lit: Mixed = "autopx";
  const num: Mixed = "5px";
}
function mixedOther(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const bad: Mixed = "zzpx";
}

// --- Unions and mixes of patterns (one string SType holds them all) ---

type PatternUnion = `#${string}` | `${number}px`;
function patternUnion(): void {
  const a: PatternUnion = "#ff";
  const b: PatternUnion = "5px";
}
function patternUnionBad(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const bad: PatternUnion = "zz";
}

type LitPlusPattern = "lit" | `#${string}`;
function litPlusPattern(): void {
  const a: LitPlusPattern = "lit";
  const b: LitPlusPattern = "#ab";
}
function litPlusPatternBad(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const bad: LitPlusPattern = "ab";
}

// `string` absorbs a pattern in a union.
type Absorbed = `#${string}` | string;
function absorbed(s: string): void {
  const u: Absorbed = s;
}

// --- A pattern used as a hole is spliced in (tsc flattens nested templates) ---

type Nested = `x${`${number}y`}z`;
function nested(): void {
  const ok: Nested = "x5yz";
}
function nestedBad(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const bad: Nested = "xyz";
}

type Flat = `${`#${string}`}px`;
function flat(): void {
  const ok: Flat = "#apx";
}
function flatBad(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const bad: Flat = "#a";
}

// --- Pattern-to-pattern assignability (tsc's relation) ---

type An = `a${number}`;
type As = `a${string}`;
function patternToPattern(an: An, as_: As): void {
  // Same texts, and `number` is a subtype of the `string` hole.
  const widened: As = an;
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const narrowed: An = as_;
}

// Different texts go through the greedy matcher: `${number}px` IS assignable
// to `${string}x` in tsc (the source's trailing "p" is carved off), but
// `a${string}` is NOT assignable to `${string}a`.
type Px2 = `${number}px`;
type Sx = `${string}x`;
type A1 = `a${string}`;
type A2 = `${string}a`;
function greedyCross(px: Px2, a1: A1): void {
  const ok: Sx = px;
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const bad: A2 = a1;
}

// --- Narrowing by === ---

function narrow(hx: Hex): void {
  if (hx === "#a") {
    const y: "#a" = hx;
  } else {
    // The else branch cannot represent "pattern minus one literal", so the
    // pattern is kept (over-approximation), as in tsc.
    const z: Hex = hx;
  }
}

// --- Indexing with a pattern key goes through the string index ---

function index(o: { [k: string]: number }, k: Hex): void {
  const v: number | undefined = o[k];
}

// --- Still rejected: an abstract hole ---

// An abstract type parameter has no known values at the definition, and the
// result would be a pattern mentioning the type variable itself.
// @skjs-expect-error Template literal types are only supported when every interpolation has finitely many values, which this one does not
type Deferred<T extends string> = `a${T}b`;
