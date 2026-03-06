// Tests that numeric string literals can access [x: number] index signatures

function testNumericStringAccessOnNumberIndex(): void {
  const obj: { [x: number]: string } = {};

  // FIXME: Numeric string access should work but SKJS rejects it
  // @skjs-expect-error Invalid index key
  const a: string | undefined = obj["0"];
  // @skjs-expect-error Invalid index key
  const b: string | undefined = obj["42"];
  // @skjs-expect-error Invalid index key
  const c: string | undefined = obj["1.5"];
  // @skjs-expect-error Invalid index key
  const d: string | undefined = obj["-1"];

  // Non-numeric string access fails
  // @skjs-expect-error Invalid index key
  const e = obj["foo"];

  // Non-canonical numeric string access fails
  // @skjs-expect-error Invalid index key
  const f = obj["01"];
}
