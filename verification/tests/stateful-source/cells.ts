function aliasWrite(seed: boolean): boolean {
  const cell: { value: boolean } = { value: seed };
  const alias: { value: boolean } = cell;
  alias.value = false;
  return cell.value;
}

function assignmentResult(): boolean {
  const cell: { value: boolean } = { value: true };
  return (cell.value = false);
}

function nestedWrite(): boolean {
  const cell: { value: boolean } = { value: true };
  cell.value = cell.value = false;
  return cell.value;
}

function branchWrite(condition: boolean): boolean {
  const cell: { value: boolean } = { value: true };
  if (condition) {
    cell.value = false;
  } else {
    cell.value = true;
  }
  return cell.value;
}

function singletonCell(): true {
  const cell: { value: true } = { value: true };
  return cell.value;
}
