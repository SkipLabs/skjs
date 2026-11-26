interface Newable {
  new (x: string): Newable;
}
declare const n: Newable;
export function use(): Newable {
  // @skjs-expect-error This expression is not constructable
  return new n("hi");
}
export function useBad(): Newable {
  // @skjs-expect-error This expression is not constructable
  return new n(42);
}
