// Normalization ownership controls. Positive cases must not be converted to
// expected errors to conceal over-sealing or recursion regressions.
type NormalizationKeys<T> = keyof { left: T; right: number };

function normalizationKeyPositive<T>(): NormalizationKeys<T> {
  return "left";
}

function normalizationKeyNegative<T>(): NormalizationKeys<T> {
  // @ts-expect-error
  return "missing";
}

type NormalizationMapped<T> = { [P in NormalizationKeys<T>]: T };

function normalizationMappedPositive<T>(x: NormalizationMapped<T>): T {
  return x.right;
}

function normalizationMappedNegative(x: NormalizationMapped<number>): string {
  // @ts-expect-error
  return x.left;
}

type NormalizationTemplate<T> = `prefix-${NormalizationKeys<T>}`;

function normalizationTemplatePositive<T>(): NormalizationTemplate<T> {
  return "prefix-right";
}

function normalizationTemplateNegative<T>(): NormalizationTemplate<T> {
  // @ts-expect-error
  return "prefix-missing";
}

function normalizationClosedPositive<T>(x: Closed<{ value: T }>): T {
  return x.value;
}

function normalizationClosedNegative(x: Closed<{ value: number }>): string {
  // @ts-expect-error
  return x.value;
}

type NormalizationElement<T> = (readonly T[] & readonly T[])[number];
declare function normalizationSelect<T>(xs: readonly T[]): NormalizationElement<T>;

function normalizationIntersectionPositive(xs: readonly number[]): number {
  return normalizationSelect(xs);
}

function normalizationIntersectionNegative(xs: readonly number[]): string {
  // @ts-expect-error
  return normalizationSelect(xs);
}

type NormalizationList<T> = null | {
  head: T;
  tail: NormalizationList<T>;
};

function normalizationRecursivePositive(
  xs: readonly NormalizationList<number>[],
): NormalizationList<number> {
  return normalizationSelect(xs);
}

type NormalizationKeyDomain = string | number;
type NormalizationDictionary<T> = { [key: NormalizationKeyDomain]: T };

function normalizationIndexPositive<T>(
  x: NormalizationDictionary<T>,
  key: number,
): T | undefined {
  return x[key];
}

declare const normalizationSymbol: unique symbol;
type NormalizationSymbolShape<T> = { [normalizationSymbol]: T };

function normalizationSymbolPositive<T>(x: NormalizationSymbolShape<T>): T {
  return x[normalizationSymbol];
}

declare const normalizationContainer: { readonly pair: readonly [number, string] };
type NormalizationDeclaredPair = typeof normalizationContainer.pair;

function normalizationTypeofPositive(x: NormalizationDeclaredPair): string {
  return x[1];
}

type NormalizationPhantom<T extends number> = { kind: "checked" };
// A materialized/erasing body must not drop a written argument's constraint.
// @ts-expect-error
type NormalizationInvalidPhantom = NormalizationPhantom<string>;

// The two functions differ only in whether this is actually receiverless.
function normalizationReceiverlessPositive(
  f: (this: void, x: number) => number,
): (x: number) => number {
  return f;
}

function normalizationReceiverNegative(
  f: (this: { value: number }, x: number) => number,
): (this: { value: string }, x: number) => number {
  // @ts-expect-error
  return f;
}
