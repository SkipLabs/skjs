// Test rest elements in array destructuring (not supported)

function testRestInArrayDestructuring(): void {
  const arr: [number, string, boolean] = [1, "hello", true];

  // @skjs-expect-error Construction not supported: Rest element in array destructuring
  const [first, ...rest] = arr;
}

function testRestInArrayDestructuringMiddle(): void {
  const arr: [number, string, boolean, number] = [1, "hello", true, 42];

  // @skjs-expect-error Construction not supported: Rest element in array destructuring
  const [first, ...rest] = arr;
}

function testRestInArrayDestructuringOnly(): void {
  const arr: [number, string] = [1, "hello"];

  // @skjs-expect-error Construction not supported: Rest element in array destructuring
  const [...rest] = arr;
}

function testRestInArrayDestructuringWithSkipped(): void {
  const arr: [number, string, boolean, number] = [1, "hello", true, 42];

  // @skjs-expect-error Construction not supported: Rest element in array destructuring
  const [, second, ...rest] = arr;
}
