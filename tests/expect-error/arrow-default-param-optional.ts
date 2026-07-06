// A default value makes a parameter optional at the call site, so a
// function with a defaulted parameter should be assignable to a function
// type whose parameter is optional (`x?`). tsc --strict accepts both the
// named and the arrow forms below.

function namedDefaultParam(x: number = 0): number {
  return x;
}

function assignNamed(): void {
  const g: (x?: number) => number = namedDefaultParam;
}

function assignArrow(): void {
  const f = (x: number = 0): number => x;
  const g: (x?: number) => number = f;
}
