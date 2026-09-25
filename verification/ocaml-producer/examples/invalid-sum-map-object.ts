// A mapper producing plain JSON arrays. TypeScript accepts it; here `map`'s
// V2 is bounded by the DepSafe that EagerCollection intersects its values
// with, and an array not managed by the runtime is not DepSafe, so the call is
// refused, a safe program among them.
import type {
  Context,
  EagerCollection,
  Mapper,
  Values,
} from "@skipruntime/core";
class Wrap implements Mapper<string, number, string, readonly number[]> {
  mapEntry(
    key: string,
    values: Values<number>,
    _context: Context,
  ): Iterable<[string, readonly number[]]> {
    return [[key, [values.getUnique()]]];
  }
}
export function wrap(
  c: EagerCollection<string, number>,
): EagerCollection<string, readonly number[]> {
  return c.map(Wrap);
}
