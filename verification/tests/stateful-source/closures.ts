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

function widenedBody(): boolean {
  const run: (unit: null) => boolean = (unit: null): boolean => true;
  return run(null);
}

function writingBody(): boolean {
  const cell: { value: boolean } = { value: true };
  const run: (unit: null) => boolean = (unit: null): boolean =>
    (cell.value = false);
  return run(null);
}

function allocatingBody(): boolean {
  const run: (unit: null) => boolean = (unit: null): boolean =>
    ({ value: true }).value;
  return run(null);
}

function callingBody(): boolean {
  const cell: { value: boolean } = { value: true };
  const read: (unit: null) => boolean = (unit: null): boolean => cell.value;
  const run: (unit: null) => boolean = (unit: null): boolean => read(null);
  cell.value = false;
  return run(null);
}

function blockReader(): boolean {
  const cell: { value: boolean } = { value: true };
  const read: (unit: null) => boolean = (unit: null): boolean => {
    return cell.value;
  };
  cell.value = false;
  return read(null);
}
