// A method is a closure, and array operations inside a closure are not yet in
// the fragment.
class Pair {
  constructor(private first: number) {}
  pair(second: number): [number, number] {
    return [this.first, second];
  }
}
export function make(): number {
  return new Pair(1).pair(2)[0];
}
