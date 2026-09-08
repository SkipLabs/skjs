function zeroTrips(flag: boolean): boolean {
  while (flag) {
    const local: boolean = flag;
  }
  return flag;
}

function oneWrite(): boolean {
  const cell: { value: boolean } = { value: true };
  const test: (x: null) => boolean = (x: null): boolean => cell.value;
  while (test(null)) {
    const alias: { value: boolean } = cell;
    alias.value = false;
  }
  return cell.value;
}

function nested(flag: boolean): boolean {
  while (flag) {
    while (flag) {
      return flag;
    }
  }
  return flag;
}
