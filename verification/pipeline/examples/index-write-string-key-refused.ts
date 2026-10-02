// A key-adding write on a local's own dictionary at a string known only at
// run time: the string may be `[]` or `[[proto]]`, keys the model keeps for
// the array store and the prototype, which JavaScript owns as ordinary
// properties. Refused.
export function set(k: string): { [k: string]: number } {
  const d: { [k: string]: number } = {};
  d[k] = 5;
  return d;
}
