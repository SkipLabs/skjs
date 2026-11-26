interface Newable {
  new (x: string): Newable;
}
declare const n: Newable;
export function use(): Newable {
  return new n("hi");
}
export function useBad(): Newable {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  return new n(42);
}

// Overloaded construct signatures with the arity filter
interface N2 {
  new (x: string): N2;
  new (x: number, y: boolean): N2;
}
declare const n2: N2;
export function use2(): void {
  const a: N2 = new n2("hi");
  const b: N2 = new n2(1, true);
}
export function use2Bad(): void {
  // @skjs-expect-error No overload matches this call
  const c: N2 = new n2(1);
}

// Merged interface declarations accumulate construct signatures
interface MN {
  new (x: string): MN;
}
interface MN {
  new (x: number): MN;
}
declare const mn: MN;
export function useMN(): void {
  const a: MN = new mn("hi");
  const b: MN = new mn(42);
}

// extends inherits construct signatures
interface B {
  new (x: string): B;
}
interface D extends B {
  new (x: number): D;
}
declare const dd: D;
export function useD(): void {
  const a: D = new dd(1);
  const b: B = new dd("hi");
}
