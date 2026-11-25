// Template literal types that denote an infinite but PARTIAL set of strings
// (patterns), issue #897: a hole over a whole primitive (`string`, `number`,
// `bigint`) surrounded by text of its own, as in `#${string}` or `${number}px`.
// Each definition below is currently rejected: SKJS represents a string type as
// either the whole primitive or a finite literal set, and a pattern is neither.

// @skjs-expect-error Template literal types are only supported when every interpolation has finitely many values, which this one does not
type Hex = `#${string}`;

// @skjs-expect-error Template literal types are only supported when every interpolation has finitely many values, which this one does not
type Px = `${number}px`;

// @skjs-expect-error Template literal types are only supported when every interpolation has finitely many values, which this one does not
type Big = `${bigint}n`;

// @skjs-expect-error Template literal types are only supported when every interpolation has finitely many values, which this one does not
type Both = `a${string}b${number}c`;

// @skjs-expect-error Template literal types are only supported when every interpolation has finitely many values, which this one does not
type MixedHole = `${number | "auto"}px`;

// @skjs-expect-error Template literal types are only supported when every interpolation has finitely many values, which this one does not
type PatternUnion = `#${string}` | `${number}px`;

// @skjs-expect-error Template literal types are only supported when every interpolation has finitely many values, which this one does not
type LitPlusPattern = "lit" | `#${string}`;

// @skjs-expect-error Template literal types are only supported when every interpolation has finitely many values, which this one does not
type Nested = `x${`${number}y`}z`;

// @skjs-expect-error Template literal types are only supported when every interpolation has finitely many values, which this one does not
type PatternHole = `${`#${string}`}px`;

// @skjs-expect-error Template literal types are only supported when every interpolation has finitely many values, which this one does not
type Greedy = `${string}-${number}`;

// An abstract type parameter has no known values at the definition, and stays
// unsupported even under #897: the pattern would have to mention the type
// variable itself.
// @skjs-expect-error Template literal types are only supported when every interpolation has finitely many values, which this one does not
type Deferred<T extends string> = `a${T}b`;
