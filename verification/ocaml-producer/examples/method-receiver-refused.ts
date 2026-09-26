// A class method declaring `this: T`: a method member's contract is relative
// to its host, the object it is read from, so a receiver stated apart from it
// has no member form. Refused where the class is read.
class Ctx {
  value: number = 1;
}
class Holder {
  m(this: Ctx, x: number): number {
    return this.value + x;
  }
}
export function call(h: Holder & Ctx): number {
  return h.m(1);
}
