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
