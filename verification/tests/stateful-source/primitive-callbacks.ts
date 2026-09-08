// Unary primitive callbacks use the existing arrow and mutable-cell semantics.
function booleanIdentity(seed: boolean): boolean {
  const identity: (value: boolean) => boolean = (value: boolean): boolean =>
    value;
  return identity(seed);
}

function unionIdentity(seed: null | boolean): null | boolean {
  const identity: (value: null | boolean) => null | boolean = (
    value: null | boolean,
  ): null | boolean => value;
  return identity(seed);
}

function capturedWriter(seed: boolean): boolean {
  const cell: { value: boolean } = { value: seed };
  const write: (next: boolean) => null = (next: boolean): null => {
    cell.value = next;
    return null;
  };
  const done: null = write(false);
  return cell.value;
}

function narrowerCallContract(): boolean {
  const acceptTrue: (value: true) => boolean = (value: boolean): true => true;
  return acceptTrue(true);
}

function returnedWriter(): (next: boolean) => boolean {
  const cell: { value: boolean } = { value: true };
  return (next: boolean): boolean => {
    cell.value = next;
    return cell.value;
  };
}

// The stable snapshot survives a callback that changes the cell.
function stableSnapshot(seed: boolean): true {
  const cell: { value: boolean } = { value: seed };
  const reset: (next: boolean) => null = (next: boolean): null => {
    cell.value = next;
    return null;
  };
  const snapshot: boolean = cell.value;
  if (snapshot) {
    const done: null = reset(false);
    return snapshot;
  }
  return true;
}
