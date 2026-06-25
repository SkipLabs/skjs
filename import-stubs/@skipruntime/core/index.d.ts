export type Json =
  | null
  | boolean
  | number
  | string
  | readonly (Json | null)[]
  | JsonObject;

export interface JsonObject {
  readonly [key: string]: Json | null;
}

export interface JsonPartialObject {
  readonly [key: string]: Json | null | undefined;
}

export type int = number;

export type Nullable<T> = T | null;

export interface Managed {}

export type DepSafe = null | boolean | number | bigint | string | Managed;

export declare function deepFreeze<T>(value: T): T & DepSafe;

export interface Mapper<
  K1 extends Json,
  V1 extends Json,
  K2 extends Json,
  V2 extends Json,
> {
  mapEntry(key: K1, values: Values<V1>, context: Context): Iterable<[K2, V2]>;
}

export interface Reducer<V extends Json, A extends Json> {
  initial: A;

  add(accum: A, value: V & DepSafe): A;

  remove(accum: A, value: V & DepSafe): Nullable<A>;
}

export declare abstract class AbstractEagerCollection implements Managed {
  protected readonly __sk_collectionBrand: undefined;
}

export declare abstract class AbstractLazyCollection implements Managed {
  protected readonly __sk_collectionBrand: undefined;
}

export interface EagerCollection<K extends Json, V extends Json>
  extends AbstractEagerCollection {
  getArray(key: K): (V & DepSafe)[];

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

  slices(
    ...ranges: readonly [K & DepSafe, K & DepSafe][]
  ): EagerCollection<K, V>;

  take(limit: int): EagerCollection<K, V>;

  merge(...others: readonly EagerCollection<K, V>[]): EagerCollection<K, V>;

  size(): number;
}

export interface LazyCollection<K extends Json, V extends Json>
  extends AbstractLazyCollection {
  getArray(key: K): (V & DepSafe)[];
}

export interface LazyCompute<K extends Json, V extends Json> {
  compute(self: LazyCollection<K, V>, key: K, context: Context): Iterable<V>;
}

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
}

export interface Values<T> extends Iterable<T & DepSafe> {
  toArray(): (T & DepSafe)[];
}

export type Entry<K extends Json, V extends Json> = [K, V[]];

export type CollectionUpdate<K extends Json, V extends Json> = {
  values: Entry<K, V>[];
  watermark: string;
  isInitial?: boolean;
};

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

export declare abstract class AbstractInputDefinition {
  protected readonly __sk_inputDefBrand: undefined;
}

export declare class InputDefinition<
  K extends Json,
  V extends Json,
> extends AbstractInputDefinition {
  public initial: Entry<K, V>[];
}

export type NamedInputDefinitions = {
  readonly [name: string]: AbstractInputDefinition;
};

export type NamedEagerCollections = {
  readonly [name: string]: AbstractEagerCollection;
};

export type SharedCollections = {
  readonly [name: string]: AbstractEagerCollection | AbstractLazyCollection;
};

export interface Resource<Collections extends SharedCollections> {
  instantiate(
    collections: Collections,
    context: Context,
  ): AbstractEagerCollection;
}

export type ResourceClass<
  Collections extends SharedCollections,
  Params extends Json,
> = new (params: Params) => Resource<Collections>;

export type NamedResources<ResourceInputs extends SharedCollections> = {
  readonly [name: string]: ResourceClass<ResourceInputs, never>;
};

export interface SkipService<
  InputDefs extends NamedInputDefinitions,
  Inputs extends NamedEagerCollections,
  ResourceInputs extends SharedCollections,
> {
  readonly inputs: InputDefs;

  readonly resources: NamedResources<ResourceInputs>;

  externalServices?: { [name: string]: ExternalService };

  createGraph(inputs: Inputs, context: Context): ResourceInputs;
}

export declare class ServiceInstance {
  instantiateResource(
    identifier: string,
    resource: string,
    params: Json,
  ): Promise<void>;

  getAll<K extends Json, V extends Json>(
    resource: string,
    params?: Json,
  ): Promise<Entry<K, V>[]>;

  getArray<K extends Json, V extends Json>(
    resource: string,
    key: K,
    params?: Json,
  ): Promise<V[]>;

  closeResourceInstance(resourceInstanceId: string): void;

  subscribe<K extends Json, V extends Json>(
    resourceInstanceId: string,
    notifier: {
      subscribed: () => void;
      notify: (update: CollectionUpdate<K, V>) => void;
      close: () => void;
    },
    watermark?: string,
  ): string;

  unsubscribe(id: string): void;

  update<K extends Json, V extends Json>(
    collection: string,
    entries: Entry<K, V>[],
  ): Promise<void>;

  close(): Promise<unknown>;
}
