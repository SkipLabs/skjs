// Test rest elements in array destructuring

// === Tuple source ===

function restFromTuple(): void {
  const tuple: [number, string, boolean] = [1, "hello", true];
  const [first, ...rest] = tuple;
  const a: number = first;
  const b: [string, boolean] = rest;
}

function restFromTupleSkipped(): void {
  const tuple: [number, string, boolean, number] = [1, "hello", true, 42];
  const [, second, ...rest] = tuple;
  const a: string = second;
  const b: [boolean, number] = rest;
}

function restAllElements(): void {
  const tuple: [number, string] = [1, "hello"];
  const [...rest] = tuple;
  const a: [number, string] = rest;
}

function restZeroRemaining(): void {
  const tuple: [number, string] = [1, "hello"];
  const [a, b, ...rest] = tuple;
  void rest;
}

// === Array/iterable source ===

function restFromArray(): void {
  const arr: number[] = [1, 2, 3];
  const [first, ...rest] = arr;
  const a: number | undefined = first;
  const b: number[] = rest;
}

// === Type error cases ===

function restTooManyBeforeRest(): void {
  const tuple: [number] = [1];
  // @skjs-expect-error Invalid tuple pattern size, it is of size 2
  const [a, b, ...rest] = tuple;
}
