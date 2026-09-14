function compoundKey(): number {
  const box = { value: 1 };
  let count = 0;
  box[(count += 1) === 1 ? "value" : "value"] += 1;
  return count;
}

function annotatedCompoundKey(): number {
  const box: { value: number } = { value: 1 };
  let count = 0;
  box[(count += 1) === 1 ? "value" : "value"] += 1;
  return count;
}
