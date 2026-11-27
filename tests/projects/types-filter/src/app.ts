function useAllowed(): number {
  return ALLOWED_VAL;
}

function badAllowed(): string {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return ALLOWED_VAL;
}

function excludedNotLoaded(): string {
  // @skjs-expect-error Cannot find name
  return EXCLUDED_VAL;
}

function builtinsStillLoaded(xs: Array<string>): number {
  return xs.length;
}
