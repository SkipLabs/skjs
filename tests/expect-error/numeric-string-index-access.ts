// Tests that numeric string literals can access [x: number] index signatures

function testNumericStringAccessOnNumberIndex(): void {
  const obj: { [x: number]: string } = {};

  // Numeric string access works
  const a: string | undefined = obj["0"];
  const b: string | undefined = obj["42"];
  const c: string | undefined = obj["1.5"];
  const d: string | undefined = obj["-1"];
}

// Non-numeric string access fails. In its own function so the
// "one error per def" rule doesn't hide the non-canonical case below.
function testNonNumericStringAccessFails(): void {
  const obj: { [x: number]: string } = {};
  // @skjs-expect-error Invalid index key: expected number, got string
  const e = obj["foo"];
}

// Non-canonical numeric strings (leading zero, etc.) also fail.
function testNonCanonicalNumericStringAccessFails(): void {
  const obj: { [x: number]: string } = {};
  // @skjs-expect-error Invalid index key: expected number, got string
  const f = obj["01"];
}
