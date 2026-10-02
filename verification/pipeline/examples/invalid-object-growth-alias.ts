// Another binding holds the object before the write: through it, the object
// was allocated without `x` and may be read as lacking it, so the write that
// would add the key is refused.
export function grow(): { x?: string } {
  const o = {};
  const alias: {} = o;
  o.x = 1;
  const seen: { x?: string } = alias;
  return seen;
}
