function alwaysTrueUndefined(x: undefined, y: undefined): boolean {
  // @ts-expect-error This equality is always true
  return x === y;
}

function alwaysTrueNull(x: null, y: null): boolean {
  // @ts-expect-error This equality is always true
  return x === y;
}

function alwaysTrueString(x: "a", y: "a"): boolean {
  // @ts-expect-error This equality is always true
  return x === y;
}

function alwaysTrueNumber(x: 0, y: 0): boolean {
  // @ts-expect-error This equality is always true
  return x === y;
}

// TODO: typeof NaN
// function alwaysFalseNaN(x: typeof NaN, y: typeof NaN): boolean {
//   // TODO: always false
//   return x === y;
// }

function alwaysFalseNumbers(x: 0, y: 1): boolean {
  // @ts-expect-error This equality is always false
  return x === y;
}

function alwaysFalseDifferentTypes(x: number, y: string): boolean {
  // @ts-expect-error This equality is always false
  return x === y;
}
