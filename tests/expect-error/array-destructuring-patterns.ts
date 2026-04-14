// Test array destructuring with skipped elements

function testSkippedElements(): void {
  const arr: [number, string, boolean] = [1, "hello", true];

  // Skip middle element
  const [first, , third] = arr;
  const x: number = first;
  const y: boolean = third;
}

function testSkippedElementsWithType(): void {
  const arr: [number, string, boolean, number] = [1, "hello", true, 42];

  // Skip multiple elements
  const [, second, , fourth] = arr;
  const a: string = second;
  const b: number = fourth;
}

function testSkippedElementsTypeError(): void {
  const arr: [number, string, boolean] = [1, "hello", true];

  const [first, , third] = arr;
  // @ts-expect-error Invalid annotation
  const x: string = first;
}

// Test tuple destructuring with defaults

function testTupleDefaultUseful(): void {
  const arr: [number | undefined, string | undefined] = [1, "hello"];
  // @skjs-expect-error Construction not supported: Default value in array destructuring (ignored)
  const [a = 0, b = "default"] = arr;
}

function testTupleDefaultUseless(): void {
  const arr: [number, string] = [1, "hello"];
  // @skjs-expect-error Construction not supported: Default value in array destructuring (ignored)
  const [a = 0, b = "default"] = arr;
}

function testTupleDefaultDifferentType(): void {
  const arr: [number | undefined] = [1];
  // @skjs-expect-error Construction not supported: Default value in array destructuring (ignored)
  const [a = "fallback"] = arr;
}

function testTupleDefaultAlwaysUndefined(): void {
  const arr: [undefined] = [undefined];
  // @skjs-expect-error Construction not supported: Default value in array destructuring (ignored)
  const [a = 42] = arr;
}

// Test array (iterable) destructuring with defaults

function testArrayDefaultUseful(): void {
  const arr: (number | undefined)[] = [1, undefined, 3];
  // @skjs-expect-error Construction not supported: Default value in array destructuring (ignored)
  const [a = 0] = arr;
}

// Test combination of skipped elements and defaults

function testSkippedWithDefaults(): void {
  const arr: [number, string | undefined, boolean] = [1, "hello", true];
  // @skjs-expect-error Construction not supported: Default value in array destructuring (ignored)
  const [first, , third = false] = arr;
}
