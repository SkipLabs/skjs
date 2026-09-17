function checkedMutableObjectReplacement(seed: boolean | null): boolean {
  let cell = { value: seed };
  const read = (): boolean => {
    if (cell.value !== null) return cell.value;
    return false;
  };
  cell = { value: null };
  return read();
}

function nestedSavedReads(seed: boolean | null): boolean {
  let cell: { value: boolean | null } | null = { value: seed };
  const read = (): boolean => {
    if (cell === null) return false;
    if (cell.value === null) return false;
    return cell.value;
  };
  cell = null;
  return read();
}
