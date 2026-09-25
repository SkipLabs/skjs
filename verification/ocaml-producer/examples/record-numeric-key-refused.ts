// `Record<number, V>` is a numeric index, outside the fragment's records.
function same(r: Record<number, string>): Record<number, string> {
  return r;
}
