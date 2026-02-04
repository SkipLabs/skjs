// Sound type bindings for Skip reactive services.
//
// Uses branded abstract base classes to model existential types, avoiding
// the unsound widening in the standard @skipruntime/core bindings.

// ===================== Core Types =====================

export type Json = null | boolean | number | string | Json[] | JsonObject;

export type JsonObject = { [key: string]: Json | null };

export type int = number;

export type Nullable<T> = T | null;

export type DepSafe =
  | null
  | boolean
  | number
  | bigint
  | string
  | Managed;

export interface Managed {}

// ===================== Context =====================

export interface Context {
  jsonExtract(value: JsonObject, pattern: string): Json[];
}

// ===================== Values =====================

export interface Values<T> extends Iterable<T & DepSafe> {
  getUnique(_default?: { ifMany?: T }): T & DepSafe;
  toArray(): (T & DepSafe)[];
}

// ===================== Entry =====================

export type Entry<K extends Json, V extends Json> = [K, V[]];

// ===================== Mapper =====================

export interface Mapper<
  K1 extends Json,
  V1 extends Json,
  K2 extends Json,
  V2 extends Json,
> {
  mapEntry(key: K1, values: Values<V1>, context: Context): Iterable<[K2, V2]>;
}

// ===================== Reducer =====================

export interface Reducer<V extends Json, A extends Json> {
  initial: Nullable<A>;
  add(accum: Nullable<A>, value: V & DepSafe): A;
  remove(accum: A, value: V & DepSafe): Nullable<A>;
}

// ===================== EagerCollection =====================

// Branded base class representing ∃K,V. EagerCollection<K,V>
export abstract class AbstractEagerCollection implements Managed {
  protected __sk_collectionBrand: undefined;
  constructor() {
    this.__sk_collectionBrand = undefined;
  }
}

export interface EagerCollection<K extends Json, V extends Json>
  extends AbstractEagerCollection {
  getArray(key: K): (V & DepSafe)[];

  getUnique(key: K, _default?: { ifNone?: V; ifMany?: V }): V & DepSafe;

  map<K2 extends Json, V2 extends Json, Params extends DepSafe[]>(
    mapper: new (...params: Params) => Mapper<K, V, K2, V2>,
    ...params: Params
  ): EagerCollection<K2, V2>;

  reduce<Accum extends Json, Params extends DepSafe[]>(
    reducer: new (...params: Params) => Reducer<V, Accum>,
    ...params: Params
  ): EagerCollection<K, Accum>;

  mapReduce<K2 extends Json, V2 extends Json, MapperParams extends DepSafe[]>(
    mapper: new (...params: MapperParams) => Mapper<K, V, K2, V2>,
    ...mapperParams: MapperParams
  ): <Accum extends Json, ReducerParams extends DepSafe[]>(
    reducer: new (...params: ReducerParams) => Reducer<V2, Accum>,
    ...reducerParams: ReducerParams
  ) => EagerCollection<K2, Accum>;

  slice(start: K & DepSafe, end: K & DepSafe): EagerCollection<K, V>;

  slices(...ranges: [K & DepSafe, K & DepSafe][]): EagerCollection<K, V>;

  take(limit: int): EagerCollection<K, V>;

  merge(...others: EagerCollection<K, V>[]): EagerCollection<K, V>;

  size(): number;
}

// ===================== InputDefinition =====================

// Branded base class representing ∃K,V. InputDefinition<K,V>
export abstract class AbstractInputDefinition {
  protected __sk_inputDefBrand: undefined;
  constructor() {
    this.__sk_inputDefBrand = undefined;
  }
}

// Defines an input collection with its initial data
export class InputDefinition<
  K extends Json,
  V extends Json,
> extends AbstractInputDefinition {
  public initial: Entry<K, V>[];

  constructor(initial: Entry<K, V>[] = []) {
    super();
    this.initial = initial;
  }
}

// ===================== Named Collections =====================

export type NamedInputDefinitions = { [name: string]: AbstractInputDefinition };

export type NamedEagerCollections = { [name: string]: AbstractEagerCollection };

// ===================== Resource =====================

export interface Resource<Collections extends NamedEagerCollections> {
  instantiate(
    collections: Collections,
    context: Context,
  ): AbstractEagerCollection;
}

// A class implementing Resource<C> with constructor taking Params
export type ResourceClass<
  Collections extends NamedEagerCollections,
  Params extends Json,
> = new (params: Params) => Resource<Collections>;

// ===================== SkipService =====================

export interface SkipService<
  InputDefs extends NamedInputDefinitions,
  Inputs extends NamedEagerCollections,
  ResourceInputs extends NamedEagerCollections,
  Resources,
> {
  inputs: InputDefs;

  resources: Resources;

  createGraph(inputs: Inputs, context: Context): ResourceInputs;
}
