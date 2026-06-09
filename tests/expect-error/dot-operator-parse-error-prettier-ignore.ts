// Test that dot operators reject non-name expressions (parse error)

function test(): void {
  const obj = { foo: 1 };
  // @skjs-expect-error 'a variable name' expected
  const a = obj.("foo");
