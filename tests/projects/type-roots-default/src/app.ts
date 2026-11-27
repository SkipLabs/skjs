function useAuto(): boolean {
  return AUTO_GLOBAL;
}

function badAuto(): number {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return AUTO_GLOBAL;
}
