// Test control flow refinement for if statements without else

// This should work - no type error expected
function testNoElseRefinement(): void {
  let apiPort: undefined | number = undefined;
  if (apiPort === undefined) {
    apiPort = 4000;
  }
  // apiPort should be refined to number here
  let result: number = apiPort; // Should not cause error
}

// This should also work - with explicit check
function testExplicitUndefinedCheck(): void {
  let value: string | undefined = undefined;
  if (value !== undefined) {
    return;
  }
  // value should still be string | undefined here since we returned
  // @ts-expect-error
  let len: number = value.length; // Should cause error since value could be undefined
}

// Test with null check
function testNullCheck(): void {
  let data: string | null = null;
  if (data === null) {
    data = "hello";
  }
  // data should be refined to string here
  let result: string = data; // Should not cause error
}

// Test nested conditions
function testNestedConditions(): void {
  let x: number | undefined = undefined;
  let y: string | undefined = undefined;

  if (x === undefined) {
    x = 42;
  }
  if (y === undefined) {
    y = "test";
  }

  // Both should be refined to their non-undefined types
  let numResult: number = x; // Should not cause error
  let strResult: string = y; // Should not cause error
}
