function useAllowed(): number {
  // @skjs-expect-error Cannot find name
  return ALLOWED_VAL;
}

function excludedNotLoaded(): string {
  // @skjs-expect-error Cannot find name
  return EXCLUDED_VAL;
}

function builtinsStillLoaded(xs: Array<string>): number {
  return xs.length;
}
