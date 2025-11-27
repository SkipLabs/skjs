// Test that dot operators only accept names, not expressions

function testDotOperators(): void {
  const obj = { foo: 1, bar: 2 };
  const key = "foo";

  // Valid: dot with name
  const a = obj.foo;
  const b = obj.bar;

  // Valid: bracket notation with expression
  const c = obj[key];
  const d = obj["foo"];
}
