class ArrowField {
  n: number = 1;
  // @skjs-expect-error 'this' is not available in this context
  m: () => number = (): number => this.n;
}
export function probeArrow(c: ArrowField): number {
  return c.m();
}

class PlainField {
  n: number = 1;
  // @skjs-expect-error 'this' is not available in this context
  k: number = this.n;
}

class LaterField {
  a: number = 1;
  // @skjs-expect-error 'this' is not available in this context
  b: number = this.c;
  c: number = 2;
}
