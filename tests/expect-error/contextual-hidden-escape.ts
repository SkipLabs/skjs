class ContextBox<T> {
  value: T;
  constructor(value: T) {
    this.value = value;
  }
}
class ContextRunner<T> {
  seed: T;
  constructor(seed: T) {
    this.seed = seed;
  }
  twice(f: (x: unknown, y?: T) => T, a: unknown, b: unknown): [T, T] {
    return [f(a), f(b)];
  }
}
function contextualRoot(a: ContextBox<number>, b: ContextBox<string>): number {
  const pair = new ContextRunner(null).twice(
    // @ts-expect-error A function signature cannot expose a locally discovered hidden type; use opaque parameter and return types
    (x, y = x instanceof ContextBox ? x : null): typeof y => y,
    a,
    b,
  );
  const p = pair[0];
  const q = pair[1];
  if (p && q) p.value = q.value;
  return a.value;
}

function opaqueContextualRoot(a: unknown, b: unknown): [unknown, unknown] {
  return new ContextRunner<unknown>(null).twice(
    (x, y = x instanceof ContextBox ? x : null): unknown => y,
    a,
    b,
  );
}
