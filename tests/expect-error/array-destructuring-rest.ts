// Test rest elements in array destructuring

// === Tuple source ===

function restFromTuple(): void {
  const tuple: [number, string, boolean] = [1, "hello", true];
  // @skjs-expect-error Construction not supported: Rest element in array destructuring
  const [first, ...rest] = tuple;
}

function restFromTupleSkipped(): void {
  const tuple: [number, string, boolean, number] = [1, "hello", true, 42];
  // @skjs-expect-error Construction not supported: Rest element in array destructuring
  const [, second, ...rest] = tuple;
}

function restAllElements(): void {
  const tuple: [number, string] = [1, "hello"];
  // @skjs-expect-error Construction not supported: Rest element in array destructuring
  const [...rest] = tuple;
}

function restZeroRemaining(): void {
  const tuple: [number, string] = [1, "hello"];
  // @skjs-expect-error Construction not supported: Rest element in array destructuring
  const [a, b, ...rest] = tuple;
}

// === Array/iterable source ===

function restFromArray(): void {
  const arr: number[] = [1, 2, 3];
  // @skjs-expect-error Construction not supported: Rest element in array destructuring
  const [first, ...rest] = arr;
}

// === Type error cases (for after implementation) ===

function restFromTupleTypeError(): void {
  const tuple: [number, string, boolean] = [1, "hello", true];
  // @skjs-expect-error Construction not supported: Rest element in array destructuring
  const [first, ...rest] = tuple;
  // TODO: rest should be [string, boolean], assigning to [number, boolean] should error
}

function restTooManyBeforeRest(): void {
  const tuple: [number] = [1];
  // @skjs-expect-error Construction not supported: Rest element in array destructuring
  const [a, b, ...rest] = tuple;
  // TODO: b should be undefined since tuple only has 1 element
}
