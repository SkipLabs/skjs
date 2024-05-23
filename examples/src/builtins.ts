declare const console: {
  log<T>(msg: T): void;
  assert(cond: boolean, msg?: string): void;
};

declare class Array<T> {
  length: number;
  find(filter: (T) => boolean): undefined | T;
  push(elt: T): void;
  indexOf(x: T): number;
  sort(f?: (object, object) => number): Array<T>;
  static isArray<T>(value: T): boolean;
}

declare const Math: {
  max: (number, number) => number;
  floor: (number) => number;
  random: () => number;
};

declare class string {
  startsWith(prefix: string): boolean;
  endsWith(suffix: string): boolean;
}

declare class Object {
  static keys(obj: object): Array<string>;
}
