function allocation(): boolean {
  const c = { value: true };
  const d: { value: boolean } = { value: true };
  return c.value && d.value;
}
