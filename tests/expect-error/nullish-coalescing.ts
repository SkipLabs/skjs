function uselessNull(x: null): number {
  // @ts-expect-error This operator is useless
  return x ?? 0;
}

function uselessUndefined(x: undefined): number {
  // @ts-expect-error This operator is useless
  return x ?? 0;
}

function uselessNullOrUndefined(x: null | undefined): number {
  // @ts-expect-error This operator is useless
  return x ?? 0;
}

function uselessNoNull(x: number): number {
  // @ts-expect-error This operator is useless
  return x ?? 0;
}

function withSameType(x: null | undefined | number): number {
  // TODO: should not be an error
  // @ts-expect-error Invalid return type
  return x ?? 0;
}

function withAnotherType(x: null | undefined | string): string | number {
  // TODO: should not be an error
  // @ts-expect-error Invalid return type
  return x ?? 0;
}

function paramTop<T>(x: T): T | number {
  return x ?? 0;
}

function uselessNullOrUndefinedParam<T extends null | undefined>(x: T): number {
  // @ts-expect-error This operator is useless
  return x ?? 0;
}

function uselessNoNullParam<T extends number>(x: T): number {
  // @ts-expect-error This operator is useless
  return x ?? 0;
}

function withSameTypeParam<T extends null | undefined | number>(x: T): number {
  // TODO: should not be an error
  // @ts-expect-error Invalid return type
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
  // TODO: should not be an error
  // @ts-expect-error Invalid return type
  return x ?? 0;
}
