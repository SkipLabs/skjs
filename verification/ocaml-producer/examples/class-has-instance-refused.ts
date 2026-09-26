// A static `[Symbol.hasInstance]` replaces the prototype-chain test that
// `instanceof` is in the model with a call: the class is refused where it is
// declared.
class Anything {
  static [Symbol.hasInstance](_x: unknown): boolean {
    return true;
  }
}
export function make(): Anything {
  return new Anything();
}
