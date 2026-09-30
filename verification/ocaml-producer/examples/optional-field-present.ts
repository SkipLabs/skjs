// A required field covers an optional one of the same key and contract,
// `number | undefined`; a readonly optional one, any field within it.
function read(value: { field?: number }): number | undefined {
  return value.field;
}
export function pass(value: { field: number | undefined }): number | undefined {
  return read(value);
}
function view(value: { readonly field?: number }): number | undefined {
  return value.field;
}
export function passView(value: { field: number }): number | undefined {
  return view(value);
}
