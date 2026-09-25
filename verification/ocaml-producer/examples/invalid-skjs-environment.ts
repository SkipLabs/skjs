// `Closed<T>` is read as `T`, which promises nothing of the keys `T` does not
// name: a closed value is not admitted where every string key must hold a
// number, though SKJS, reading the absence of other keys, accepts it.
type Point = Closed<{ x: number }>;

export function asIndex(p: Point): { [k: string]: number } {
  return p;
}
