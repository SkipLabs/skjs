function scenario(cell: { value: boolean }): number {
  let count = 0;
  const limit = 10;
  count = count + 1;
  cell.value = true;
  let x: boolean | number = 1;
  if (typeof x === "number") {
    x = x + 1;
  }
  return count + limit;
}
