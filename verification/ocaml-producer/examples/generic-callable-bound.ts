// A generic identity satisfies a monomorphic callable bound.
export function use(flag: boolean): boolean {
  const choose = <T extends (x: boolean) => boolean>(fn: T): T => fn;
  const id = <U>(value: U): U => value;
  return choose(id)(flag);
}
