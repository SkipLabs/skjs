function makeAdder(delta: number): (n: number) => number {
  return (n: number): number => {
    const next = n + delta;
    return next;
  };
}

function incrTwice(x: number): number {
  const incr = (n: number): number => n + 1;
  return incr(incr(x));
}

function classify(n: number): string {
  const label = (m: number): string => {
    if (m < 0) {
      return "negative";
    }
    return "nonneg";
  };
  return label(n);
}

function apply(f: (n: number) => number, x: number): number {
  return f(x);
}

function useCallback(x: number): number {
  return apply((n: number): number => {
    const doubled = n * 2;
    return doubled;
  }, x);
}

function iife(x: number): number {
  return ((n: number): number => n + 1)(x);
}

function makeAdderFactory(): (a: number) => (b: number) => number {
  return (a: number) => (b: number) => a + b;
}
