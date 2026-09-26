// A generic class method: its closure's claim would be a quantified callable,
// which the claim format does not encode.
class Helper {
  pick<V>(a: V): V {
    return a;
  }
}
export function use(h: Helper): number {
  return h.pick(1);
}
