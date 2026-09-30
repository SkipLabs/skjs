// A writable optional field `field?: number` holds `number | undefined` where
// the object has the key, which its holder may write: a field holding only
// numbers does not establish it. (TypeScript accepts the call.)
function read(value: { field?: number }): number | undefined {
  return value.field;
}
export function pass(value: { field: number }): number | undefined {
  return read(value);
}
