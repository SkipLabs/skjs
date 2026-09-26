// `then` infers its binders through `TResult | PromiseLike<TResult>` and a
// default: refused by name.
export function show(p: Promise<number>): Promise<string> {
  return p.then((n: number) => n.toString());
}
