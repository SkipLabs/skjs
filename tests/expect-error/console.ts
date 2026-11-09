function unsupportedConsoleApis(): void {
  // @skjs-expect-error Property 'table' does not exist on this type
  console.table("data");
}

// `console.assert` only logs (it does not throw), so its condition proves
// nothing: no narrowing follows (issue #1042). tsc's lib declares no
// assertion signature for it either.
function consoleAssertDoesNotNarrow(x: string | null): void {
  console.assert(x !== null);
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const s: string = x;
}
