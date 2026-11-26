interface Callable {
  (x: string): number;
  (x: string, y: number): string;
}
declare const c: Callable;
export function use(): void {
  const a: number = c("hi");
  const b: string = c("hi", 1);
}
export function useBad(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const bad: string = c("hi");
}
export function useBad2(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const bad: number = c("hi", 1);
}

// Generic call signature
interface G {
  <T>(x: T): T;
}
declare const g: G;
export function useG(): void {
  const s: string = g("hi");
}
export function useGBad(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const bad: number = g("hi");
}

// Merged interface declarations accumulate call signatures
interface M {
  (x: string): number;
}
interface M {
  (x: number): string;
}
declare const m: M;
export function useM(): void {
  const a: number = m("hi");
  const b: string = m(42);
}

// extends: own signatures resolve before inherited ones (derived-first, like tsc)
interface Base {
  (x: string | number): number;
}
interface Derived extends Base {
  (x: string): string;
}
declare const d: Derived;
export function useD(): void {
  const s: string = d("hi");
  const n: number = d(42);
}

// A matching function inhabits a callable interface; a non-callable object does not
interface Single {
  (x: string): number;
}
export function useSingle(): void {
  const f: Single = (x: string): number => 1;
}
export function useSingleBad(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const bad: Single = { m: 1 };
}
