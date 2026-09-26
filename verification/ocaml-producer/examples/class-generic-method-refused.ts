// A generic class method: the instance's member has quantified signatures,
// which its prototype's closure, a scheme received by the instance, is not
// yet related to (DESIGN, next steps).
class Helper {
  pick<V>(a: V): V {
    return a;
  }
}
export function use(h: Helper): number {
  return h.pick(1);
}
