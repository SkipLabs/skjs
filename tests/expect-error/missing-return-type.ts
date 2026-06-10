// Functions must declare explicit return types.
// @skjs-expect-error Function 'missingReturnType' must have an explicit return type annotation
function missingReturnType() {
  return 1;
}

function takesCallback(cb: (x: number) => number): void {
  const result: number = cb(1);
}

function returnAnnotated(): number {
  return 1;
}

function useCallbacks(): void {
  takesCallback((value: number): number => value + 1);
}
