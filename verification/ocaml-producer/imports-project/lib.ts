// A library whose values the examples import. Nothing here is checked by the
// verifier: each import is assumed at the type its declaration states.
export function double(x: number): number {
  return x + x;
}
export const limit: number = 10;
export class Counter {
  count: number;
  constructor(start: number) {
    this.count = start;
  }
  bump(): number {
    this.count = this.count + 1;
    return this.count;
  }
}
export function generic<T>(x: T): T {
  return x;
}
export class Holder<T> {
  value: T;
  constructor(value: T) {
    this.value = value;
  }
}
export class Keeper<T> {
  value: T;
  constructor(value: T) {
    this.value = value;
  }
  get(): T {
    return this.value;
  }
}
export class Tagged {
  readonly tag: number = 1;
}
export class Named extends Tagged {
  readonly name: string = "named";
}
// Two brands, keyed by distinct unique symbols: a value carries one brand's
// key and not the other's.
export const brand: unique symbol = Symbol("brand");
export const other: unique symbol = Symbol("other");
export type Branded = { [brand]: true; n: number };
export type Marked = { [other]: true; n: number };
export function wrap(n: number): Branded {
  return { [brand]: true, n };
}
export function mark(n: number): Marked {
  return { [other]: true, n };
}
export function unwrap(b: Branded): number {
  return b.n;
}
// Generic methods: `pick` returns one of its arguments, at the type a call
// instantiates; a `Cell`'s `with` makes a cell of another type.
export interface Chooser {
  pick<T>(first: T, second: T): T;
}
export const chooser: Chooser = { pick: (first, second) => first };
export interface Cell<T> {
  readonly value: T;
  with<U>(value: U): Cell<U>;
}
export function cell<T>(value: T): Cell<T> {
  return { value, with: (next) => cell(next) };
}
// A generic method with a bounded binder: `either` returns one of two
// Booleans, at the Boolean type a call instantiates.
export interface Flags {
  either<T extends boolean>(first: T, second: T): T;
}
export const flags: Flags = { either: (first, second) => first };
