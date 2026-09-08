// Negation preserves the identity of immutable Boolean tests, with reversed arms.
function negatedBranch(flag: boolean): true {
  if (!flag) {
    return true;
  }
  return flag;
}

function doubleNegatedBranch(flag: boolean): false {
  if (!!flag) {
    return false;
  }
  return flag;
}

function negatedClosure(flag: boolean): true {
  const choose: (x: boolean) => true = (x: boolean): true => {
    if (!x) {
      return true;
    }
    return x;
  };
  return choose(flag);
}

// The callback mutates the cell: its operand must be evaluated exactly once.
function negatedCall(): boolean {
  const cell: { value: boolean } = { value: false };
  const toggle: (x: null) => boolean = (x: null): boolean => {
    const before: boolean = cell.value;
    cell.value = !before;
    return before;
  };
  const result: boolean = !toggle(null);
  return cell.value;
}

function negatedLoop(): boolean {
  const cell: { value: boolean } = { value: false };
  const test: (x: null) => boolean = (x: null): boolean => cell.value;
  while (!test(null)) {
    cell.value = true;
    continue;
  }
  return cell.value;
}
