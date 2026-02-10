// Test that unsupported features have specific error messages

class TestUnsupportedFeatures {
  // Test postfix ! operator (not supported)
  testPostfixExclamation(): void {
    let x: boolean | null = true;
    // @skjs-expect-error Do not use the postfix ! operator
    const y: boolean = x!;
  }

  // Test non-null assertion on member access (not supported)
  testNonNullAssertion(): void {
    // @skjs-expect-error Invalid annotation
    const obj: { value: number } | null = { value: 5 };
    // @skjs-expect-error Do not use the postfix ! operator
    const x: number = obj!.value;
  }
}

// Test as operator (not supported)
function testAsOperator(): void {
  const x: unknown = 5;
  // @skjs-expect-error Construction not supported: operator as
  const y: number = x as number;
}
