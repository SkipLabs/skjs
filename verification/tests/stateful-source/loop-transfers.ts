function stopAfterWrite(): boolean {
  const cell: { value: boolean } = { value: true };
  const test: (x: null) => boolean = (x: null): boolean => cell.value;
  while (test(null)) {
    const alias: { value: boolean } = cell;
    alias.value = false;
    break;
  }
  return cell.value;
}

function continueAfterWrite(): boolean {
  const cell: { value: boolean } = { value: true };
  const test: (x: null) => boolean = (x: null): boolean => cell.value;
  while (test(null)) {
    const alias: { value: boolean } = cell;
    alias.value = false;
    continue;
  }
  return cell.value;
}

function nestedBreak(flag: boolean): boolean {
  while (flag) {
    while (flag) {
      const local: boolean = flag;
      break;
    }
    return true;
  }
  return false;
}

function branchContinue(flag: boolean): boolean {
  const cell: { value: boolean } = { value: true };
  const test: (x: null) => boolean = (x: null): boolean => cell.value;
  while (test(null)) {
    if (flag) {
      cell.value = false;
      continue;
    }
    break;
  }
  return cell.value;
}
