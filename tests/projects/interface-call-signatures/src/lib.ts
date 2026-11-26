// An exported callable/constructable interface: importers must see the
// call/construct signatures and resolve first-match-wins.
export interface Callable {
  (x: string): number;
  (x: number): string;
}
export interface Newable {
  new (x: string): Newable;
}
