function skippedWrite(flag: boolean): number {
  let value: number | null = null;
  flag ||= (value = 1) === 1;
  // @ts-expect-error Type of returned value is not assignable to the function's return type
  return value;
}
function localFallback(value: number | null): number {
  value ??= 1;
  return value;
}
