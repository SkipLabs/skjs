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

function testTupleDefaults(): void {
  // @skjs-expect-error TODO optional element tuple
  const arr: [number?, string?] = [1, "hello"];

  const [a = 0, b = "default"] = arr;
  const x: number = a;
  const y: string = b;
}

function testTupleDefaultsTypeInference(): void {
  // @skjs-expect-error TODO optional element tuple
  const arr: [number?, string?] = [1, "hello"];

  // Default value types should combine with tuple element types
  const [a = 99, b = "fallback"] = arr;
  const x: number = a;
  const y: string = b;
}

function testTupleDefaultsTypeError(): void {
  // @skjs-expect-error TODO optional element tuple
  const arr: [number?, string?] = [1, "hello"];

  const [a = 0, b = "default"] = arr;
  // TODO: Invalid assignment (not reported due to earlier error in function)
  const x: string = a;
}

// Test combination of skipped elements and defaults

function testSkippedWithDefaults(): void {
  // @skjs-expect-error TODO optional element tuple
  const arr: [number?, string?, boolean?] = [1, "hello", true];

  const [, second = "default", third = false] = arr;
  const x: string = second;
  const y: boolean = third;
}

function testComplexPattern(): void {
  // @skjs-expect-error TODO optional element tuple
  const arr: [number, string?, boolean?, number?] = [1, "a", true, 42];

  const [first, , third = false, fourth = 0] = arr;
  const a: number = first;
  const b: boolean = third;
  const c: number = fourth;
}
