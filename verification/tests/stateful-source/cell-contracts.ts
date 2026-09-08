// Contract-export fixture only; source allocation/read/write lowering is next.
function mutableCell(cell: { value: boolean }): boolean {
  return cell.value;
}

function literalCell(cell: { value: true }): true {
  return cell.value;
}

function readonlyCell(cell: { readonly value: boolean }): boolean {
  return cell.value;
}

function optionalCell(cell: { value?: boolean }): boolean | undefined {
  return cell.value;
}

function otherField(cell: { other: boolean }): boolean {
  return cell.other;
}

function extraField(cell: { value: boolean; other: null }): boolean {
  return cell.value;
}

function nestedCell(cell: { value: { value: boolean } }): boolean {
  return cell.value.value;
}

function allocatedCell(seed: boolean): boolean {
  const cell: { value: boolean } = { value: seed };
  const alias: { value: boolean } = cell;
  alias.value = false;
  return cell.value;
}

function indexedCell(cell: {
  value: boolean;
  [key: string]: boolean;
}): boolean {
  return cell.value;
}

function allocatedLiteral(): true {
  const cell: { value: true } = { value: true };
  return cell.value;
}

function allocatedWidened(): boolean {
  const cell: { value: boolean } = { value: true };
  return cell.value;
}

function genericCell<T>(cell: { value: T }): T {
  return cell.value;
}
