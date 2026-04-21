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
    const obj: { value: number } | null = { value: 5 };
    // @skjs-expect-error Do not use the postfix ! operator
    const x: number = obj!.value;
  }
}

// Test as operator: only sound upcasts are accepted; downcasts error
function testAsOperator(): void {
  const x: unknown = 5;
  // @skjs-expect-error Unsound 'as' cast
  const y: number = x as number;
}
