// `JSON.stringify` returns `undefined` for `undefined` and throws on a bigint,
// though declared to return a string: it is not in the reviewed overlay.
function encode(n: number): string {
  return JSON.stringify(n);
}
