// A generic class method: it would be a host-relative member with quantified
// signatures, which the model does not have.
class Helper {
  pick<V>(a: V): V {
    return a;
  }
}
export function use(h: Helper): number {
  return h.pick(1);
}
