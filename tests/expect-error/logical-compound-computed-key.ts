function computedFallback(): number {
  const box: { value: number | null } = { value: null };
  let count = 0;
  return (box[(count += 1) === 1 ? "value" : "value"] ??= 1);
}
function computedAnd(flag: boolean): boolean {
  const box: { value: boolean } = { value: flag };
  let count = 0;
  return (box[(count += 1) === 1 ? "value" : "value"] &&= false);
}
