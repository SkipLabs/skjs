// `typeof x === "object"` also holds for null: it is no shape test, and a
// `typeof` result used as a string value is not inferred yet.
export function isObject(x: { a: number } | number | null): boolean {
  return typeof x === "object";
}
