class Cell {
  value: boolean = false;
}
function readValue(): boolean {
  const c = new Cell();
  return c.value;
}
