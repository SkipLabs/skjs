// Test that dot operators reject non-name expressions (parse error)

function test(): void {
  const obj = { foo: 1 };
  // @ts-expect-error Expected token a variable name
  const a = obj.("foo");
