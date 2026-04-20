// Test the TypeScript `satisfies` operator.
// `satisfies` asserts that an expression's inferred type is assignable to a
// given type, but (unlike an annotation) does NOT widen the inferred type.

// Basic: expression conforms to the target type
function testBasic(): void {
  // @skjs-expect-error Construction not supported: operator satisfies
  const x = 42 satisfies number;
}

// Subtype failure: expression is NOT assignable to the target type
function testSubtypeFailure(): void {
  // @skjs-expect-error Construction not supported: operator satisfies
  const x = "hello" satisfies number;
}

// Literal preservation: the inferred literal type survives through `satisfies`
function testLiteralPreservation(): void {
  // @skjs-expect-error Construction not supported: operator satisfies
  const s = "foo" satisfies string;
  const narrow: "foo" = s;
}

// Object: target type has wider fields, but inferred field types stay narrow
function testObjectPreservation(): void {
  // @skjs-expect-error Construction not supported: operator satisfies
  const config = { port: 8080, host: "localhost" } satisfies {
    port: number;
    host: string;
  };
  const port: 8080 = config.port;
  const host: "localhost" = config.host;
}

// Nested `satisfies`
function testNested(): void {
  // @skjs-expect-error Construction not supported: operator satisfies
  const obj = { x: 1 satisfies number };
}
