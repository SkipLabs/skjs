// `catch<TResult>` returns `Promise<T | TResult>`: every call's result adds
// a binder, so the graph truncates the family at a colour budget, and an
// instance of the binder is truncated one level before the type it is
// claimed at.
export function recover(p: Promise<number>): Promise<number> {
  return p.catch((reason: unknown) => 0);
}
