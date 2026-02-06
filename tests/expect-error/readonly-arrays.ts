type RONumbers = readonly number[];

function readonlyArrayRead(a: RONumbers): number | undefined {
  return a[0];
}

function readonlyArrayWriteIndex(a: RONumbers): void {
  // @skjs-expect-error Invalid assignment
  a[0] = 1;
}

function readonlyArrayMutatingMethod(a: RONumbers): void {
  // @skjs-expect-error Invalid call
  a.push(1);
  // @skjs-expect-error Invalid call
  const _ignored: number | undefined = a.pop();
  // @skjs-expect-error Invalid call
  a["push"](1);
}

function readonlyArrayMutatingMethodExtraction(a: RONumbers): void {
  // @skjs-expect-error Invalid annotation
  const p: (x: number) => number = a.push;
  // @skjs-expect-error Invalid call
  p(1);
}

function readonlyArrayNonMutatingMethods(a: RONumbers): number {
  const mapped: number[] = a.map((x: number) => x + 1);
  const sliced = a.slice(0, 1);
  return (mapped[0] ?? 0) + (sliced[0] ?? 0);
}

function mutableToReadonly(a: number[]): RONumbers {
  return a;
}

function readonlyToMutable(a: RONumbers): number[] {
  // @skjs-expect-error Invalid return type
  return a;
}
