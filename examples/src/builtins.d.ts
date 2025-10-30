declare const console: {
  log<T>(...msg: T[]): void;
  assert(cond: boolean, msg?: string): void;
  error(message?: unknown, ...optionalParams: unknown[]): void;
};

/* It's not really the interface but for now it will do the trick given
   that our Iterables are Arrays only. */
declare interface Iterable<T> {
  [i: number]: T;
}

declare interface ArrayLike<T> {
  /*readonly*/ length: number;
  /*readonly*/ [n: number]: T;
}

declare class Array<T> implements Iterable<T> {
  constructor(...items: T[]);
  length: number;

  [index: number]: T;

  // Existing methods
  find(filter: (item: T) => boolean): undefined | T;
  push(elt: T): void;
  indexOf(x: T): number;
  sort(f?: (a: object, b: object) => number): Array<T>;
  map<T2>(f: (item: T) => T2): Array<T2>;
  filter(f: (item: T) => boolean): Array<T>;
  reduce<U>(f: (acc: U, item: T) => U, initial: U): U;
  static isArray<T>(value: T): boolean;
  join(separator: string): string;
  slice(start: number, end?: number): Array<T>;

  // Additional essential Array methods
  pop(): T | undefined;
  shift(): T | undefined;
  unshift(element: T): number;
  splice(start: number, deleteCount?: number): Array<T>;
  concat(other: Array<T>): Array<T>;
  reverse(): Array<T>;
  includes(element: T): boolean;
  lastIndexOf(element: T): number;
  every(predicate: (item: T) => boolean): boolean;
  some(predicate: (item: T) => boolean): boolean;
  forEach(callback: (item: T, index: number) => void): void;
  findIndex(predicate: (item: T) => boolean): number;
  fill(value: T, start?: number, end?: number): Array<T>;
  copyWithin(target: number, start: number, end?: number): Array<T>;
  flatMap<U>(mapper: (item: T) => Array<U>): Array<U>;
  reduceRight<U>(reducer: (acc: U, item: T) => U, initial: U): U;

  // Static methods
  static from<T>(arrayLike: ArrayLike<T> | Iterable<T>): Array<T>;
  // If we have overloads:
  // static from<T, U>(arrayLike: Array<T>, mapFn: (item: T) => U): Array<U>;
  static of<T>(...elements: T[]): Array<T>;
}

declare const Math: {
  // Mathematical constants
  PI: number;
  E: number;
  LN2: number;
  LN10: number;
  LOG2E: number;
  LOG10E: number;
  SQRT1_2: number;
  SQRT2: number;

  // Existing methods
  max: (a: number, b: number) => number;
  min: (a: number, b: number) => number;
  floor: (x: number) => number;
  ceil: (x: number) => number;
  round: (x: number) => number;
  abs: (x: number) => number;
  pow: (x: number, y: number) => number;
  sqrt: (x: number) => number;
  random: () => number;

  // Additional essential Math methods
  acos: (x: number) => number;
  acosh: (x: number) => number;
  asin: (x: number) => number;
  asinh: (x: number) => number;
  atan: (x: number) => number;
  atan2: (y: number, x: number) => number;
  atanh: (x: number) => number;
  cbrt: (x: number) => number;
  clz32: (x: number) => number;
  cos: (x: number) => number;
  cosh: (x: number) => number;
  exp: (x: number) => number;
  expm1: (x: number) => number;
  fround: (x: number) => number;
  hypot: (x: number, y: number) => number;
  imul: (x: number, y: number) => number;
  log: (x: number) => number;
  log1p: (x: number) => number;
  log2: (x: number) => number;
  log10: (x: number) => number;
  sign: (x: number) => number;
  sin: (x: number) => number;
  sinh: (x: number) => number;
  tan: (x: number) => number;
  tanh: (x: number) => number;
  trunc: (x: number) => number;
};

declare class boolean {
  toString(): string;
}

declare class number {
  toString(): string;
  toFixed(digits?: number): string;
  toExponential(fractionDigits?: number): string;
  toPrecision(precision?: number): string;
  valueOf(): number;
}

// Number object for static access (e.g., Number.MAX_VALUE)
declare const Number: {
  MAX_VALUE: number;
  MIN_VALUE: number;
  POSITIVE_INFINITY: number;
  NEGATIVE_INFINITY: number;
  NaN: number;
  MAX_SAFE_INTEGER: number;
  MIN_SAFE_INTEGER: number;
  EPSILON: number;

  isFinite(value: number): boolean;
  isInteger(value: number): boolean;
  isNaN(value: number): boolean;
  isSafeInteger(value: number): boolean;
  parseFloat(string: string): number;
  parseInt(string: string, radix?: number): number;
};

declare class string {
  length: number;

  [index: number]: string | undefined;

  // Existing methods
  charAt(pos: number): string;
  startsWith(prefix: string): boolean;
  endsWith(suffix: string): boolean;
  substring(start: number, end?: number): string;
  indexOf(searchString: string): number;
  split(separator: string): Array<string>;
  toLowerCase(): string;
  toUpperCase(): string;

  // Additional essential String methods
  charCodeAt(index: number): number;
  concat(str: string): string;
  includes(searchString: string): boolean;
  lastIndexOf(searchString: string): number;
  localeCompare(compareString: string): number;
  match(regexp: string): Array<string> | undefined;
  padEnd(targetLength: number, padString?: string): string;
  padStart(targetLength: number, padString?: string): string;
  repeat(count: number): string;
  replace(searchValue: string, replaceValue: string): string;
  search(regexp: string): number;
  slice(start: number, end?: number): string;
  substr(start: number, length?: number): string;
  toString(): string;
  trim(): string;
  trimEnd(): string;
  trimStart(): string;
  valueOf(): string;
}

declare const String: {
  // Static methods
  fromCharCode(code: number): string;
};

declare class Object {
  // Existing methods
  static keys(obj: object): Array<string>;

  // Additional Object utility methods
  static values<T>(obj: { [s: string]: T }): Array<T>;
  static entries<T>(obj: { [s: string]: T }): Array<[string, T]>;
  static assign<T extends object, U>(target: T, source: U): T & U;
  // static create<T>(prototype: T): T; // disallowed
  // static defineProperty<T>(obj: T, prop: string, descriptor: object): T;
  // static freeze<T>(obj: T): T;
  static getOwnPropertyNames<T>(obj: T): Array<string>;
  static getOwnPropertyDescriptor<T>(obj: T, prop: string): object | undefined;
  // static getPrototypeOf<T>(obj: T): T; // disallowed
  static isExtensible<T>(obj: T): boolean;
  static isFrozen<T>(obj: T): boolean;
  static isSealed<T>(obj: T): boolean;
  static preventExtensions<T>(obj: T): T;
  static seal<T>(obj: T): T;
  // static setPrototypeOf<T, U>(obj: T, prototype: U): T; // disallowed

  // Instance methods
  toString(): string;
  valueOf(): object;
  hasOwnProperty(prop: string): boolean;
  isPrototypeOf<T>(obj: T): boolean;
  propertyIsEnumerable(prop: string): boolean;
}

// Define the MapIterator interface
interface MapIterator<T> {
  // Core iteration protocol
  next(): { value: T; done: boolean };

  // Functional utility methods
  map<U>(fn: (value: T) => U): MapIterator<U>;
  filter(predicate: (value: T) => boolean): MapIterator<T>;
  forEach(fn: (value: T) => void): void;
  toArray(): T[];
  take(n: number): MapIterator<T>;
  drop(n: number): MapIterator<T>;
  some(predicate: (value: T) => boolean): boolean;
  every(predicate: (value: T) => boolean): boolean;
  find(predicate: (value: T) => boolean): T | undefined;
}

// Updated Map class declaration
declare class Map<K, V> {
  constructor(elts?: Array<[K, V]>);
  size: number;

  // Existing methods
  get(key: K): V | undefined;
  set(key: K, value: V): void;

  // Additional Map methods
  clear(): void;
  delete(key: K): void;
  entries(): MapIterator<[K, V]>;
  forEach(callback: (value: V, key: K) => void): void;
  has(key: K): boolean;
  keys(): MapIterator<K>;
  values(): MapIterator<V>;
}

declare class Set<T> {
  constructor(values?: Array<T>);
  size: number;

  // Set methods
  add(value: T): void;
  clear(): void;
  delete(value: T): void;
  entries(): Array<[T, T]>;
  forEach(callback: (value: T) => void): void;
  has(value: T): boolean;
  keys(): Array<T>;
  values(): Array<T>;
}

declare class WeakMap<K, V> {
  constructor();
  delete(key: K): boolean;
  get(key: K): V | undefined;
  has(key: K): boolean;
  set(key: K, value: V): WeakMap<K, V>;
}

declare class WeakSet<T> {
  constructor();
  add(value: T): WeakSet<T>;
  delete(value: T): boolean;
  has(value: T): boolean;
}

declare class Date {
  constructor(
    year?: number,
    month?: number,
    day?: number,
    hour?: number,
    minute?: number,
    second?: number,
    millisecond?: number,
  );

  // Instance methods
  getDate(): number;
  getDay(): number;
  getFullYear(): number;
  getHours(): number;
  getMilliseconds(): number;
  getMinutes(): number;
  getMonth(): number;
  getSeconds(): number;
  getTime(): number;
  getTimezoneOffset(): number;
  getUTCDate(): number;
  getUTCDay(): number;
  getUTCFullYear(): number;
  getUTCHours(): number;
  getUTCMilliseconds(): number;
  getUTCMinutes(): number;
  getUTCMonth(): number;
  getUTCSeconds(): number;
  setDate(date: number): number;
  setFullYear(year: number, month?: number, date?: number): number;
  setHours(
    hours: number,
    minutes?: number,
    seconds?: number,
    milliseconds?: number,
  ): number;
  setMilliseconds(milliseconds: number): number;
  setMinutes(minutes: number, seconds?: number, milliseconds?: number): number;
  setMonth(month: number, date?: number): number;
  setSeconds(seconds: number, milliseconds?: number): number;
  setTime(time: number): number;
  setUTCDate(date: number): number;
  setUTCFullYear(year: number, month?: number, date?: number): number;
  setUTCHours(
    hours: number,
    minutes?: number,
    seconds?: number,
    milliseconds?: number,
  ): number;
  setUTCMilliseconds(milliseconds: number): number;
  setUTCMinutes(
    minutes: number,
    seconds?: number,
    milliseconds?: number,
  ): number;
  setUTCMonth(month: number, date?: number): number;
  setUTCSeconds(seconds: number, milliseconds?: number): number;
  toDateString(): string;
  toISOString(): string;
  toJSON(): string;
  toLocaleDateString(): string;
  toLocaleString(): string;
  toLocaleTimeString(): string;
  toString(): string;
  toTimeString(): string;
  toUTCString(): string;
  valueOf(): number;

  // Static methods
  static now(): number;
  static parse(s: string): number;
  static UTC(
    year: number,
    month: number,
    date?: number,
    hours?: number,
    minutes?: number,
    seconds?: number,
    ms?: number,
  ): number;
}

declare const JSON: {
  parse<T>(text: string): T;
  stringify<T>(
    value: T,
    replacer?: (key: string, value: T) => T,
    space?: string | number,
  ): string;
};

declare class RegExp {
  constructor(pattern: string, flags?: string);

  // Properties
  global: boolean;
  ignoreCase: boolean;
  multiline: boolean;
  source: string;
  lastIndex: number;

  // Methods
  exec(str: string): Array<string> | undefined;
  test(str: string): boolean;
  toString(): string;
}

declare class bigint {
  // Instance methods (all verified to exist in real JavaScript)
  toString(radix?: number): string;
  valueOf(): bigint;
  toLocaleString(): string;
}

// BigInt constructor function
declare function BigInt(value: number | string | boolean | bigint): bigint;

declare class Error {
  constructor(cause?: string);
}

declare type Record<K extends string, V> = {
  [index: K]: V;
};

/* from undici-types/fetch.d.ts */

declare class undici_BodyMixin {
  // readonly body: ReadableStream | null
  // readonly bodyUsed: boolean

  // readonly arrayBuffer: () => Promise<ArrayBuffer>
  // readonly blob: () => Promise<Blob>
  // readonly bytes: () => Promise<Uint8Array>
  // readonly formData: () => Promise<FormData> // deprecated
  readonly json: () => Promise<unknown>;
  readonly text: () => Promise<string>;
}

declare class undici_Response extends undici_BodyMixin {
  // constructor (body?: BodyInit, init?: ResponseInit)

  // readonly headers: Headers
  readonly ok: boolean;
  readonly status: number;
  readonly statusText: string;
  // readonly type: ResponseType
  readonly url: string;
  readonly redirected: boolean;

  readonly clone: () => undici_Response;

  static error(): undici_Response;
  // static json (data: any, init?: ResponseInit): Response
  // static redirect (url: string | URL, status: ResponseRedirectStatus): Response
}

declare function fetch(input: string): Promise<undici_Response>;

declare interface ProcessEnv {
  [key: string]: string | undefined;
  TZ?: string;
}

declare const process: {
  argv: string[];
  cwd(): string;
  env: ProcessEnv;
  exit(status: number): never;
};
