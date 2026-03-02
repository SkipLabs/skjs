export interface Context {
  createLazyCollection<
    K extends Json,
    V extends Json,
    Params extends readonly DepSafe[],
  >(
    compute: new (...params: Params) => LazyCompute<K, V>,
    ...params: Params
  ): LazyCollection<K, V>;

  useExternalResource<K extends Json, V extends Json>(resource: {
    service: string;
    identifier: string;
    params?: Json;
  }): EagerCollection<K, V>;

  jsonExtract(value: JsonObject, pattern: string): Json[];
}

export declare function deepFreeze<T>(value: T): T & DepSafe;

export type DepSafe =
  | null
  | boolean
  | number
  | bigint
  | string
  //   | symbol
  | Managed;

export interface EagerCollection<K extends Json, V extends Json>
  extends Managed {
  getArray(key: K): (V & DepSafe)[];

  getUnique(key: K, _default?: { ifNone?: V; ifMany?: V }): V & DepSafe;

  map<K2 extends Json, V2 extends Json, Params extends readonly DepSafe[]>(
    mapper: new (...params: Params) => Mapper<K, V, K2, V2>,
    ...params: Params
  ): EagerCollection<K2, V2>;

  reduce<Accum extends Json, Params extends readonly DepSafe[]>(
    reducer: new (...params: Params) => Reducer<V, Accum>,
    ...params: Params
  ): EagerCollection<K, Accum>;

  mapReduce<
    K2 extends Json,
    V2 extends Json,
    MapperParams extends readonly DepSafe[],
  >(
    mapper: new (...params: MapperParams) => Mapper<K, V, K2, V2>,
    ...mapperParams: MapperParams
  ): <Accum extends Json, ReducerParams extends readonly DepSafe[]>(
    reducer: new (...params: ReducerParams) => Reducer<V2, Accum>,
    ...reducerParams: ReducerParams
  ) => EagerCollection<K2, Accum>;

  slice(start: K & DepSafe, end: K & DepSafe): EagerCollection<K, V>;

  slices(...ranges: [K & DepSafe, K & DepSafe][]): EagerCollection<K, V>;

  take(limit: int): EagerCollection<K, V>;

  merge(...others: EagerCollection<K, V>[]): EagerCollection<K, V>;

  size(): number;
}

export type Entry<K extends Json, V extends Json> = [K, V[]];

export interface ExternalService {
  subscribe(
    instance: string,
    resource: string,
    params: Json,
    callbacks: {
      update: (updates: Entry<Json, Json>[], isInit: boolean) => Promise<void>;
      error: (error: unknown) => void;
    },
  ): Promise<void>;

  unsubscribe(instance: string): void;

  shutdown(): Promise<void>;
}

// export type InitialData<Inputs extends NamedCollections> = {
//   [Name in keyof Inputs]: Inputs[Name] extends EagerCollection<infer K, infer V>
//     ? Entry<K, V>[]
//     : Entry<Json, Json>[];
// };
export type InitialData<_Inputs extends NamedCollections> = {
  [name: string]: Entry<Json, Json>[];
};

export type int = number;

export type Json =
  | boolean
  | number
  | string
  | readonly (Json | null)[]
  | JsonObject;

export type JsonObject = { readonly [key: string]: Json | null };

export interface LazyCollection<K extends Json, V extends Json>
  extends Managed {
  getArray(key: K): (V & DepSafe)[];

  getUnique(key: K, _default?: { ifNone?: V; ifMany?: V }): V & DepSafe;
}

export interface LazyCompute<K extends Json, V extends Json> {
  compute(self: LazyCollection<K, V>, key: K, context: Context): Iterable<V>;
}

export interface Managed {
  //   [sk_managed]: true;
}

export interface Mapper<
  K1 extends Json,
  V1 extends Json,
  K2 extends Json,
  V2 extends Json,
> {
  mapEntry(key: K1, values: Values<V1>, context: Context): Iterable<[K2, V2]>;
}

export type NamedCollections = { [name: string]: EagerCollection<Json, Json> };

export type Nullable<T> = T | null;

export interface Reducer<V extends Json, A extends Json> {
  initial: Nullable<A>;

  add(accum: Nullable<A>, value: V & DepSafe): A;

  remove(accum: A, value: V & DepSafe): Nullable<A>;
}

export interface Resource<
  Collections extends NamedCollections /* = NamedCollections */,
> {
  instantiate(
    collections: Collections,
    context: Context,
  ): EagerCollection<Json, Json>;
}

export interface SkipService<
  Inputs extends NamedCollections /* = NamedCollections */,
  ResourceInputs extends NamedCollections /* = NamedCollections */,
> {
  initialData?: InitialData<Inputs>;

  externalServices?: { [name: string]: ExternalService };

  resources: {
    [name: string]: new (params: Json) => Resource<ResourceInputs>;
  };

  createGraph(inputCollections: Inputs, context: Context): ResourceInputs;
}

// export declare const sk_managed: unique symbol;

export interface Values<T> extends Iterable<T & DepSafe> {
  getUnique(_default?: { ifMany?: T }): T & DepSafe;

  toArray(): (T & DepSafe)[];
}
