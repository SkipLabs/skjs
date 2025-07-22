declare const console: {
  log<T>(msg: T): void;
  assert(cond: boolean, msg?: string): void;
};

declare class Array<T> {
  length: number;
  find(filter: (item: T) => boolean): undefined | T;
  push(elt: T): void;
  indexOf(x: T): number;
  sort(f?: (a: object, b: object) => number): Array<T>;
  map<T2>(f: (item: T) => T2): Array<T2>;
  static isArray<T>(value: T): boolean;
  get(idx: number): T;
}

declare const Math: {
  max: (a: number, b: number) => number;
  floor: (x: number) => number;
  random: () => number;
};

declare class boolean {
  toString(): string;
}

declare class number {
  toString(): string;
}

declare class string {
  length: number;
  charAt(pos: number): string;
  startsWith(prefix: string): boolean;
  endsWith(suffix: string): boolean;
}

declare class Object {
  static keys(obj: object): Array<string>;
}

declare class Map<K, V> {
  constructor(elts: Array<[K, V]>);
  get(key: K): V;
  set(key: K, value: V): void;
}
