function capturedRead(seed: boolean): boolean {
  const cell: { value: boolean } = { value: seed };
  const read: (unit: null) => boolean = (unit: null): boolean => cell.value;
  const alias: { value: boolean } = cell;
  alias.value = false;
  return read(null);
}

function captureOlder(): true {
  const value: true = true;
  const other: false = false;
  const read: (unit: null) => true = (unit: null): true => value;
  return read(null);
}

function escapingReader(seed: boolean): (unit: null) => boolean {
  const cell: { value: boolean } = { value: seed };
  return (unit: null): boolean => cell.value;
}
