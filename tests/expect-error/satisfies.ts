// Test the TypeScript `satisfies` operator.
// `satisfies` asserts that an expression's inferred type is assignable to a
// given type, but (unlike an annotation) does NOT widen the inferred type.

// Basic: expression conforms to the target type
function testBasic(): void {
  const x = 42 satisfies number;
}

// Subtype failure: expression is NOT assignable to the target type
function testSubtypeFailure(): void {
  // @skjs-expect-error Type does not satisfy the expected type
  const x = "hello" satisfies number;
}

// Literal preservation: with a `const` binding, the literal type survives
function testLiteralPreservation(): void {
  const s = "foo" satisfies string;
  const narrow: "foo" = s;
}

// Object field preservation: widened target type doesn't widen inferred fields
function testObjectPreservation(): void {
  const config = { port: 8080, host: "localhost" } satisfies {
    port: number;
    host: string;
  };
  const port: 8080 = config.port;
  const host: "localhost" = config.host;
}

// Nested `satisfies`
function testNested(): void {
  const obj = { x: 1 satisfies number };
}

function satisfiesAlias(x: { value: number | null }): number {
  if (x.value === null) return 0;
  // @ts-expect-error Type of value is not assignable to the variable's type annotation
  const alias: { readonly value: number } = x satisfies unknown;
  x.value = null;
  return alias.value;
}

function satisfiesStored(x: { value: number | null }): number {
  if (x.value === null) return 0;
  const alias = x satisfies unknown;
  x.value = null;
  // @ts-expect-error Type of returned value is not assignable to the function's return type
  return alias.value;
}

function satisfiesSnapshot(x: { value: number | null }): number {
  if (x.value === null) return 0;
  const value = x.value satisfies number;
  x.value = null;
  return value;
}
