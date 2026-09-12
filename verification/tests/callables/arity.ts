/** A multi-argument call must select its callee first, then evaluate arguments
 * left to right, then enter the body. The expected result is true: the first
 * argument observes true, the second false, and the body observes true again.
 * Reordering arguments or running the body before the second argument changes
 * the result. This remains a source-boundary fixture until argument lists land. */
function argumentOrder(): boolean {
  const cell: { value: boolean } = { value: false };
  // prettier-ignore
  const choose: () => (first: boolean, second: boolean) => boolean =
    (): (first: boolean, second: boolean) => boolean => {
      cell.value = true;
      return (first: boolean, second: boolean): boolean => first && !second && cell.value;
    };
  const first: () => boolean = (): boolean => {
    const old: boolean = cell.value;
    cell.value = false;
    return old;
  };
  const second: () => boolean = (): boolean => {
    const old: boolean = cell.value;
    cell.value = true;
    return old;
  };
  return choose()(first(), second());
}
