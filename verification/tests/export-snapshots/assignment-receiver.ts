function capturedWrite(seed: boolean): () => boolean {
  const cell = { value: seed };
  return (): boolean => (cell.value = !seed);
}
