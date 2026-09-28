function compoundKey(): number {
  const box = { value: 1 };
  let count = 0;
  // FIXME: inferred literal-field widening also rejects ordinary read/write assignments.
  // @skjs-expect-error Type is not assignable to the assignment target's type
  box[(count += 1) === 1 ? "value" : "value"] += 1;
  return count;
}

function annotatedCompoundKey(): number {
  const box: { value: number } = { value: 1 };
  let count = 0;
  box[(count += 1) === 1 ? "value" : "value"] += 1;
  return count;
}
