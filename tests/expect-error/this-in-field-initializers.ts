class ArrowField {
  n: number = 1;
  m: () => number = (): number => this.n;
}
export function probeArrow(c: ArrowField): number {
  return c.m();
}

class PlainField {
  n: number = 1;
  k: number = this.n;
}

class LaterField {
  a: number = 1;
  // FIXME: tsc accepts this, but `c` is still undefined when `b`'s
  // initializer runs, so SKJS rejects the read (soundness).
  // @skjs-expect-error Property 'c' does not exist on this type
  b: number = this.c;
  c: number = 2;
}
