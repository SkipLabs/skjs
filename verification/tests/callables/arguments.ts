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
