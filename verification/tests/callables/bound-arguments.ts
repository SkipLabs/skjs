/** Binding saves an argument value while the closure retains a live cell. */
function boundArguments(seed: boolean): boolean {
  const cell = { value: seed };
  const target = (saved: boolean, later: boolean): boolean =>
    saved ? (cell.value ? later : !later) : cell.value ? !later : later;
  const bound = target.bind((cell.value = !seed), cell.value);
  cell.value = seed;
  return bound(seed);
}

/** Fully binding produces a nullary closure that can escape its creator. */
function boundFactory(seed: boolean): () => boolean {
  const target = (first: boolean, second: null): boolean => first;
  return target.bind(null, seed, null);
}
