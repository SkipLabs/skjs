function bindResult(
  target: (first: boolean, second: null) => boolean,
  saved: boolean,
): (second: null) => boolean {
  return target.bind(null, saved);
}
