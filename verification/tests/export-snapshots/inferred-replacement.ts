function checkedMutableObjectReplacement(seed: boolean | null): boolean {
  let cell = { value: seed };
  const read = (): boolean => {
    if (cell.value !== null) return cell.value;
    return false;
  };
  cell = { value: null };
  return read();
}
