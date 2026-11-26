function useCustomGlobal(): string {
  // @skjs-expect-error Cannot find name
  return CUSTOM_GLOBAL;
}

function useCustomHelper(): boolean {
  // @skjs-expect-error Cannot find name
  return customHelper(42);
}

function defaultNotLoaded(): number {
  // @skjs-expect-error Cannot find name
  return DEFAULT_IGNORED;
}

function builtinsStillLoaded(xs: Array<number>): number {
  return xs.length;
}
