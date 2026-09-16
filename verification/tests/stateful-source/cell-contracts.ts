/**
 * Export a mutable Boolean field with matching read and write contracts. This
 * fixture tests contract decoding separately from whole-source verification.
 */
function mutableCell(cell: { value: boolean }): boolean {
  return cell.value;
}

/**
 * Export an exact true-only cell contract. The decoder must preserve the
 * singleton rather than widen it to Boolean.
 */
function literalCell(cell: { value: true }): true {
  return cell.value;
}

/**
 * Export a readonly field. Its access contract must not be silently treated as
 * a mutable invariant cell.
 */
function readonlyCell(cell: { readonly value: boolean }): boolean {
  return cell.value;
}

/**
 * Export an optional field whose read may be undefined. The bounded cell
 * decoder must reject this unsupported contract.
 */
function optionalCell(cell: { value?: boolean }): boolean | undefined {
  return cell.value;
}

/**
 * Preserve a field name other than value through export and decoding.
 */
function otherField(cell: { other: boolean }): boolean {
  return cell.other;
}

/**
 * Export a record with an extra field. The decoder must not silently discard
 * part of the contract.
 */
function extraField(cell: { value: boolean; other: null }): boolean {
  return cell.value;
}

/**
 * Export a cell containing another cell. Nested reference contracts are
 * outside the current primitive-cell decoder.
 */
function nestedCell(cell: { value: { value: boolean } }): boolean {
  return cell.value.value;
}

/**
 * Inspect the inferred contract of a fresh allocation and its alias after a
 * write. Both exports must retain the same Boolean invariant.
 */
function allocatedCell(seed: boolean): boolean {
  const cell: { value: boolean } = { value: seed };
  const alias: { value: boolean } = cell;
  alias.value = false;
  return cell.value;
}

/**
 * Export a real string index signature. It must be distinguished from
 * synthetic index metadata on fresh plain objects.
 */
function indexedCell(cell: {
  value: boolean;
  [key: string]: boolean;
}): boolean {
  return cell.value;
}

/**
 * Inspect a fresh allocation with a true-only annotation. Its exported cell
 * contract must retain that singleton.
 */
function allocatedLiteral(): true {
  const cell: { value: true } = { value: true };
  return cell.value;
}

/**
 * Inspect a true initializer under a Boolean field annotation. The exported
 * invariant must allow later false writes, rather than describe only the
 * initial value.
 */
function allocatedWidened(): boolean {
  const cell: { value: boolean } = { value: true };
  return cell.value;
}

/**
 * Export a field contract containing a type parameter. The bounded decoder
 * must not invent a primitive interpretation for an unsupported parameter.
 */
function genericCell<T>(cell: { value: T }): T {
  return cell.value;
}
