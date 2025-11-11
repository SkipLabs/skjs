// Functions must declare explicit return types.
// @ts-expect-error Missing return type
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
