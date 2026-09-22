// Safe JavaScript: this closure reads the same parameter binding after its
// initializer runs, rather than capturing the raw undefined argument value.
function deferredDefaultCapture(seed: boolean): boolean {
  const pick = (
    read: () => boolean = (): boolean => later,
    later: boolean = seed,
  ): boolean => read();
  return pick();
}
