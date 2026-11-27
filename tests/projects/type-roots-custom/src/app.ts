function useCustomGlobal(): string {
  return CUSTOM_GLOBAL;
}

function useCustomHelper(): boolean {
  return customHelper(42);
}

function badCustomHelper(): boolean {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  return customHelper("nope");
}

function defaultNotLoaded(): number {
  // @skjs-expect-error Cannot find name
  return DEFAULT_IGNORED;
}

function builtinsStillLoaded(xs: Array<number>): number {
  return xs.length;
}
