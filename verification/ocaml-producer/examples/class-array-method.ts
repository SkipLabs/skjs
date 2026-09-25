// The method's body verifies; the call does not yet: its declared result and
// the claimed one are two rows for `[number, number]`, and a bound member
// meets exactly its own signatures.
class Pair {
  constructor(private first: number) {}
  pair(second: number): [number, number] {
    return [this.first, second];
  }
}
export function make(): number {
  return new Pair(1).pair(2)[0];
}
