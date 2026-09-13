function uselessNull(x: null): number {
  // @skjs-expect-warning This operator has no effect; the operand is always null or undefined
  return x ?? 0;
}

function uselessUndefined(x: undefined): number {
  // @skjs-expect-warning This operator has no effect; the operand is always null or undefined
  return x ?? 0;
}

function uselessNullOrUndefined(x: null | undefined): number {
  // @skjs-expect-warning This operator has no effect; the operand is always null or undefined
  return x ?? 0;
}

function uselessNoNull(x: number): number {
  // @skjs-expect-warning This operator has no effect; the operand is never null or undefined
  return x ?? 0;
}

function withSameType(x: null | undefined | number): number {
  return x ?? 0;
}

function withAnotherType(x: null | undefined | string): string | number {
  return x ?? 0;
}

function paramTop<T>(x: T): T | number {
  return x ?? 0;
}

function uselessNullOrUndefinedParam<T extends null | undefined>(x: T): number {
  // @skjs-expect-warning This operator has no effect; the operand is always null or undefined
  return x ?? 0;
}

function uselessNoNullParam<T extends number>(x: T): number {
  // @skjs-expect-warning This operator has no effect; the operand is never null or undefined
  return x ?? 0;
}

function withSameTypeParam<T extends null | undefined | number>(x: T): number {
  return x ?? 0;
}

function withAnotherTypeParamT<T extends null | undefined | string>(
  x: T,
): T | number {
  return x ?? 0;
}

function withAnotherTypeParamMorePrecise<T extends null | undefined | string>(
  x: T,
): string | number {
  return x ?? 0;
}

function skippedFallback(seed: number | undefined): number {
  let state: number | null = null;
  const result = seed ?? (state = 1);
  // FIXME: a supplied seed skips the assignment, leaving state null.
  return state;
}

function possibleFallback(seed: number | undefined): number {
  let state: number | null = 1;
  const result = seed ?? (state = null);
  // The fallback's possible write must survive the branch merge.
  // @ts-expect-error Type of returned value is not assignable to the function's return type
  return state;
}

function resultOfFallback(seed: number | undefined): number {
  let state: number | null = null;
  const result = seed ?? (state = 1);
  // The expression produces a number even though state may remain null.
  return result;
}
