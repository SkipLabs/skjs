// Module B's generic Box<T> has the same name and arity as Module A's Box<T>
// but an incompatible shape (`b: T` instead of `a: T`).
export interface Box<T> {
  b: T;
  next: Box<T> | null;
  self(): Box<T>;
}

export function takeBoxB(x: Box<number>): number {
  return x.b;
}

export class Cell<T> {
  b: T;
  constructor(x: T) {
    this.b = x;
  }
}

export function takeCellB(x: Cell<number>): number {
  return x.b;
}
