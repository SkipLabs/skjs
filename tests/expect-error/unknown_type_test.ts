// Test for unknown type support
function testUnknownType(): void {
  let x: unknown = 42;
  let y: unknown = "hello";
  let z: unknown = true;

  acceptsUnknown(x);
  acceptsUnknown(y);
  acceptsUnknown(z);
  acceptsUnknown({});
  acceptsUnknown([]);
  acceptsUnknown(null);

  let result: unknown = returnsUnknown();
}

function acceptsUnknown(param: unknown): void {
  // unknown can accept any value
}

// Function returning unknown
function returnsUnknown(): unknown {
  return "could be anything";
}
