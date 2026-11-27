// Module A's generic Box<T> has field `a: T` and a self-reference so
// nested/method occurrences remain unexpanded TSInst nodes during subtyping.
export interface Box<T> {
  a: T;
  next: Box<T> | null;
  self(): Box<T>;
}

export declare function makeBoxA<T>(x: T): Box<T>;

export class Cell<T> {
  a: T;
  constructor(x: T) {
    this.a = x;
  }
  get(): T {
    return this.a;
  }
  set(x: T): void {
    this.a = x;
  }
}

export function makeCellA<T>(x: T): Cell<T> {
  return new Cell(x);
}

export interface Node<T> {
  value: T;
  next: Node<T> | null;
}

export function makeNode<T>(value: T): Node<T> {
  return { value, next: null };
}
