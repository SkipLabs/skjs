/**
 * A locally checked callback crosses an argument boundary. The invoking closure
 * supplies true; the callback mutates its captured cell and returns its old value.
 */
function callableArgument(seed: boolean): boolean {
  const cell: { value: boolean } = { value: seed };
  const exchange: (next: boolean) => boolean = (next: boolean): boolean => {
    const old: boolean = cell.value;
    cell.value = next;
    return old;
  };
  const invoke: (f: (next: boolean) => boolean) => boolean = (
    f: (next: boolean) => boolean,
  ): boolean => f(true);
  const old: boolean = invoke(exchange);
  return old ? cell.value : false;
}

/**
 * A callback parameter escapes inside a returned wrapper, then crosses another
 * argument boundary. The eventual call must forward its argument and observe
 * the captured cell after the intervening write, not at wrapper creation.
 */
function escapedCallbackArgument(seed: boolean): boolean {
  const cell: { value: boolean } = { value: seed };
  const exchange: (next: boolean) => boolean = (next: boolean): boolean => {
    const old: boolean = cell.value;
    cell.value = next;
    return old;
  };
  // SKJS requires an unparenthesized callable result annotation.
  // prettier-ignore
  const wrap: (f: (next: boolean) => boolean) => (next: boolean) => boolean =
    (f: (next: boolean) => boolean): (next: boolean) => boolean =>
      (next: boolean): boolean => f(next);
  const invoke: (f: (next: boolean) => boolean) => boolean = (
    f: (next: boolean) => boolean,
  ): boolean => f(seed);
  const wrapped = wrap(exchange);
  cell.value = !seed;
  const old: boolean = invoke(wrapped);
  return old;
}
