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

function localBlock(): boolean {
  const run: (unit: null) => boolean = (unit: null): boolean => {
    const cell: { value: boolean } = { value: true };
    const saved: boolean = false;
    cell.value = saved;
    return cell.value;
  };
  return run(null);
}

function branchingClosure(flag: boolean): true {
  const run: (unit: null) => true = (unit: null): true => {
    if (flag) {
      return flag;
    } else {
      return true;
    }
  };
  return run(null);
}

function nestedBranches(flag: boolean, other: boolean): boolean {
  const run: (unit: null) => boolean = (unit: null): boolean => {
    const saved: boolean = other;
    if (flag) {
      if (saved) {
        return saved;
      } else {
        const result: boolean = false;
        return result;
      }
    } else {
      return flag;
    }
  };
  return run(null);
}

function capturedBranch(): boolean {
  const cell: { value: boolean } = { value: true };
  const read: (unit: null) => boolean = (unit: null): boolean => cell.value;
  const run: (unit: null) => boolean = (unit: null): boolean => {
    if (read(null)) {
      return true;
    } else {
      return false;
    }
  };
  cell.value = false;
  return run(null);
}

function joinedClosure(flag: boolean): boolean {
  const run: (unit: null) => boolean = (unit: null): boolean => {
    const cell: { value: boolean } = { value: true };
    if (flag) {
      const saved: boolean = flag;
      cell.value = saved;
    } else {
      cell.value = false;
    }
    return cell.value;
  };
  return run(null);
}

function nestedFallThrough(flag: boolean, other: boolean): boolean {
  const run: (unit: null) => boolean = (unit: null): boolean => {
    const cell: { value: boolean } = { value: true };
    if (flag) {
      if (other) {
        cell.value = false;
      }
    }
    const saved: boolean = cell.value;
    return saved;
  };
  return run(null);
}

function earlyReturn(flag: boolean): boolean {
  const run: (unit: null) => boolean = (unit: null): boolean => {
    if (flag) {
      return flag;
    }
    return flag;
  };
  return run(null);
}

function earlyReturnElse(flag: boolean): boolean {
  const run: (unit: null) => boolean = (unit: null): boolean => {
    const cell: { value: boolean } = { value: true };
    if (flag) {
      const saved: boolean = false;
      cell.value = saved;
    } else {
      return flag;
    }
    const saved: boolean = cell.value;
    return saved;
  };
  return run(null);
}

function successiveReturns(flag: boolean, other: boolean): boolean {
  const run: (unit: null) => boolean = (unit: null): boolean => {
    if (flag) {
      return flag;
    }
    if (other) {
      return other;
    }
    return other;
  };
  return run(null);
}
