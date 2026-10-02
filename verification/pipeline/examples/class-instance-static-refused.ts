// A class's statics are bindings it defines after its methods and its
// constructor, whose closures cannot hold them: an instance method reading
// one is refused.
class Counter {
  static readonly step: number = 1;
  n: number = 0;
  next(): number {
    return this.n + Counter.step;
  }
}

export function use(c: Counter): number {
  return c.next();
}
