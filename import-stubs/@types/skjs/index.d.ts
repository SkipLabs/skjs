declare const console: {
  log(...msg: unknown[]): void;
  assert(cond: boolean, msg?: string): void;
  error(message?: unknown, ...optionalParams: unknown[]): void;
};

declare const crypto: {
  randomUUID(): string;
};

declare interface Iterable<T> {
  [Symbol.iterator](): { next(): { readonly value: T; done: boolean } };
}

declare interface ArrayLike<T> {
  readonly length: number;
  readonly [n: number]: T;
}

declare interface ReadonlyArray<T> extends Iterable<T> {
  readonly __SKJS_isArray: true;
  readonly length: number;
  readonly [n: number]: T;

  // Read-only queries
  find(filter: (item: T) => boolean): undefined | T;
  // T in contravariant position prevents covariant subtyping of ReadonlyArray.
  // indexOf(x: T): number;
  // includes(element: T): boolean;
  // lastIndexOf(element: T): number;
  every(predicate: (item: T) => boolean): boolean;
  some(predicate: (item: T) => boolean): boolean;
  forEach(callback: (item: T, index: number) => void): void;
  findIndex(predicate: (item: T) => boolean): number;
  join(separator: string): string;

  // Pure transforms
  // Returns Array<T2> (not ReadonlyArray<T2>) since map creates a fresh
  // mutable array; sound because T2 is a fresh per-call generic unrelated to
  // T, unlike filter/slice below whose return reuses T itself.
  map<T2>(f: (item: T) => T2): Array<T2>;
  filter(f: (item: T) => boolean): ReadonlyArray<T>;
  // Callback returns Array<U> (not ReadonlyArray<U>) to avoid T in contravariant
  // position. Return is also Array<U> since flatMap creates a fresh mutable array.
  flatMap<U>(mapper: (item: T) => Array<U>): Array<U>;

  // Folds
  reduce<U>(f: (acc: U, item: T) => U, initial: U): U;
  reduceRight<U>(reducer: (acc: U, item: T) => U, initial: U): U;

  // Slicing / combining (still pure)
  slice(start?: number, end?: number): ReadonlyArray<T>;
  // T in contravariant position prevents covariant subtyping from Array to ReadonlyArray.
  // concat(other: ReadonlyArray<T>): ReadonlyArray<T>;
}

declare interface SKJS_ArrayAndTupleBase<T> extends ReadonlyArray<T> {
  indexOf(x: T): number;
  map<T2>(f: (item: T) => T2): Array<T2>;
  filter(f: (item: T) => boolean): Array<T>;
  slice(start?: number, end?: number): Array<T>;
  concat(other: Array<T>): Array<T>;
  includes(element: T): boolean;
  lastIndexOf(element: T): number;
  flatMap<U>(mapper: (item: T) => Array<U>): Array<U>;
}

/* `SKJS_Tuple<U>` and `SKJS_ReadonlyTuple<U>` are the bases that the
 * synthesized `SKJS_TupleN<...>` / `SKJS_ReadonlyTupleN<...>` classes
 * (built in FileDefs#getAll) extend to pick up the array methods,
 * indexes, and the `__SKJS_isArray` brand. */
declare interface SKJS_ReadonlyTuple<U> extends ReadonlyArray<U> {}
declare interface SKJS_Tuple<U> extends SKJS_ArrayAndTupleBase<U> {}

declare class Array<T> implements SKJS_ArrayAndTupleBase<T> {
  readonly __SKJS_isArray: true;
  constructor(...items: T[]);
  length: number;

  [index: number]: T;

  // Existing methods
  find(filter: (item: T) => boolean): undefined | T;
  push(elt: T): void;
  indexOf(x: T): number;
  sort(f?: (a: T, b: T) => number): SKJS_Ignorable<Array<T>>;
  map<T2>(f: (item: T) => T2): Array<T2>;
  filter(f: (item: T) => boolean): Array<T>;
  reduce<U>(f: (acc: U, item: T) => U, initial: U): U;
  static isArray<T>(value: T): boolean;
  join(separator: string): string;
  slice(start?: number, end?: number): Array<T>;

  // Additional essential Array methods
  pop(): T | undefined;
  shift(): T | undefined;
  unshift(element: T): number;
  splice(start: number, deleteCount?: number): SKJS_Ignorable<Array<T>>;
  concat(other: Array<T>): Array<T>;
  reverse(): SKJS_Ignorable<Array<T>>;
  includes(element: T): boolean;
  lastIndexOf(element: T): number;
  every(predicate: (item: T) => boolean): boolean;
  some(predicate: (item: T) => boolean): boolean;
  forEach(callback: (item: T, index: number) => void): void;
  findIndex(predicate: (item: T) => boolean): number;
  fill(value: T, start?: number, end?: number): SKJS_Ignorable<Array<T>>;
  copyWithin(
    target: number,
    start: number,
    end?: number,
  ): SKJS_Ignorable<Array<T>>;
  flatMap<U>(mapper: (item: T) => Array<U>): Array<U>;
  reduceRight<U>(reducer: (acc: U, item: T) => U, initial: U): U;

  // Static methods
  static from<T>(arrayLike: ArrayLike<T> | Iterable<T>): Array<T>;
  // If we have overloads:
  // static from<T, U>(arrayLike: Array<T>, mapFn: (item: T) => U): Array<U>;
  static of<T>(...elements: T[]): Array<T>;

  [Symbol.iterator](): { next(): { readonly value: T; done: boolean } };
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
  max: (...values: number[]) => number;
  min: (...values: number[]) => number;
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
  // Call signature for Number(value) conversion
  (value?: unknown): number;

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
  // Call signature for String(value) conversion
  (value?: unknown): string;
  // Static methods
  fromCharCode(code: number): string;
};

declare class symbol {
  toString(): string;
  valueOf(): symbol;
}

declare const Symbol: {
  // Call signature for Symbol(description?) creation
  (description?: string | number): symbol;
  // Static methods
  for(key: string): symbol;
  keyFor(sym: symbol): string | undefined;
  // Well-known symbols
  readonly iterator: unique symbol;
  readonly asyncIterator: unique symbol;
  readonly toStringTag: unique symbol;
  readonly hasInstance: unique symbol;
  readonly isConcatSpreadable: unique symbol;
  readonly match: unique symbol;
  readonly matchAll: unique symbol;
  readonly replace: unique symbol;
  readonly search: unique symbol;
  readonly species: unique symbol;
  readonly split: unique symbol;
  readonly toPrimitive: unique symbol;
  readonly unscopables: unique symbol;
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
  next(): { readonly value: T; done: boolean };

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

  [Symbol.iterator](): MapIterator<T>;
}

// Updated Map class declaration
declare class Map<K, V> {
  constructor(elts?: Array<[K, V]> | Iterable<[K, V]>);
  size: number;

  // Existing methods
  get(key: K): V | undefined;
  set(key: K, value: V): void;

  // Additional Map methods
  clear(): void;
  delete(key: K): boolean;
  entries(): MapIterator<[K, V]>;
  forEach(callback: (value: V, key: K) => void): void;
  has(key: K): boolean;
  keys(): MapIterator<K>;
  values(): MapIterator<V>;

  [Symbol.iterator](): { next(): { readonly value: [K, V]; done: boolean } };
}

declare class Set<T> {
  constructor(values?: Array<T> | Iterable<T>);
  size: number;

  // Set methods
  add(value: T): void;
  clear(): void;
  delete(value: T): void;
  entries(): MapIterator<[T, T]>;
  forEach(callback: (value: T) => void): void;
  has(value: T): boolean;
  keys(): MapIterator<T>;
  values(): MapIterator<T>;

  [Symbol.iterator](): { next(): { readonly value: T; done: boolean } };
}

declare class WeakMap<K, V> {
  constructor();
  delete(key: K): boolean;
  get(key: K): V | undefined;
  has(key: K): boolean;
  set(key: K, value: V): SKJS_Ignorable<WeakMap<K, V>>;
}

declare class WeakSet<T> {
  constructor();
  add(value: T): SKJS_Ignorable<WeakSet<T>>;
  delete(value: T): boolean;
  has(value: T): boolean;
}

declare class Date {
  // TODO: skjs doesn't support constructor overloads, so `year` accepts
  // `string | number` to cover both the single-argument ISO-string form and
  // the multi-argument numeric form. This wrongly also accepts a string
  // `year` combined with numeric `month`/`day`/etc (e.g. `new Date("2020-01",
  // 1)`), a combination the real Date constructor doesn't support — see
  // tests/expect-error/date-constructor-string.ts.
  constructor(
    year?: string | number,
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
  setDate(date: number): SKJS_Ignorable<number>;
  setFullYear(
    year: number,
    month?: number,
    date?: number,
  ): SKJS_Ignorable<number>;
  setHours(
    hours: number,
    minutes?: number,
    seconds?: number,
    milliseconds?: number,
  ): SKJS_Ignorable<number>;
  setMilliseconds(milliseconds: number): SKJS_Ignorable<number>;
  setMinutes(
    minutes: number,
    seconds?: number,
    milliseconds?: number,
  ): SKJS_Ignorable<number>;
  setMonth(month: number, date?: number): SKJS_Ignorable<number>;
  setSeconds(seconds: number, milliseconds?: number): SKJS_Ignorable<number>;
  setTime(time: number): SKJS_Ignorable<number>;
  setUTCDate(date: number): SKJS_Ignorable<number>;
  setUTCFullYear(
    year: number,
    month?: number,
    date?: number,
  ): SKJS_Ignorable<number>;
  setUTCHours(
    hours: number,
    minutes?: number,
    seconds?: number,
    milliseconds?: number,
  ): SKJS_Ignorable<number>;
  setUTCMilliseconds(milliseconds: number): SKJS_Ignorable<number>;
  setUTCMinutes(
    minutes: number,
    seconds?: number,
    milliseconds?: number,
  ): SKJS_Ignorable<number>;
  setUTCMonth(month: number, date?: number): SKJS_Ignorable<number>;
  setUTCSeconds(seconds: number, milliseconds?: number): SKJS_Ignorable<number>;
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

// The minimal thenable shape, as in lib.es5. Callbacks return
// `U | PromiseLike<U>` (not `U | Promise<U>`) both here and in Promise so
// that Promise<T> <: PromiseLike<T> holds.
declare interface PromiseLike<T> {
  then<U>(onfulfilled: (value: T) => U | PromiseLike<U>): PromiseLike<U>;
}

// T must appear only covariantly in instance members so Promise<A> <:
// Promise<B> iff A <: B; `catch` therefore introduces its own U instead of
// mentioning T on the callback side (as lib.es5 does). The constructor and
// statics live on the value side and do not affect instance variance.
declare class Promise<T> {
  constructor(
    executor: (
      resolve: (value: T) => void,
      reject: (reason: unknown) => void,
    ) => void,
  );
  then<U>(onfulfilled: (value: T) => U | PromiseLike<U>): Promise<U>;
  catch<U>(onrejected: (reason: unknown) => U | PromiseLike<U>): Promise<T | U>;
  finally(onfinally: () => void): Promise<T>;
  static resolve<T>(value: T): Promise<T>;
  static reject(reason: unknown): Promise<never>;
  static all<T>(values: ReadonlyArray<Promise<T>>): Promise<Array<T>>;
}

declare type StringRecord<V> = {
  [index: string]: V;
};

declare type Record<K extends string | number | symbol, V> = { [P in K]: V };

type NonNullable<T> = T & {};

/* SKJS hacks */

type SKJS_Ignorable<T> = T; // & { __SKJS_Ignorable: void };

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
