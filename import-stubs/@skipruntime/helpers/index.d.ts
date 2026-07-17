import type {
  Json,
  Entry,
  ExternalService,
  Nullable,
  Reducer,
} from "@skipruntime/core";

export declare function defaultParamEncoder(params: Json): string;

export interface PolledHTTPResource {
  url: string;
  interval: number;
  conv: (data: Json) => Entry<Json, Json>[];
  encodeParams?: (params: Json) => string;
  options?: {
    headers?: { [header: string]: string };
    timeout?: number;
  };
}

export declare class PolledExternalService implements ExternalService {
  constructor(resources: { [resource: string]: PolledHTTPResource });

  subscribe(
    instance: string,
    resourceName: string,
    params: Json,
    callbacks: {
      update: (updates: Entry<Json, Json>[], isInit: boolean) => Promise<void>;
      error: (error: unknown) => void;
    },
  ): Promise<void>;

  unsubscribe(instance: string): void;

  shutdown(): Promise<void>;
}

export declare class SkipExternalService implements ExternalService {
  constructor(url: string, control_url: string);

  static direct(entrypoint: Entrypoint): SkipExternalService;

  subscribe(
    instance: string,
    resource: string,
    params: Json,
    callbacks: {
      update: (
        updates: Entry<Json, Json>[],
        isInitial: boolean,
      ) => Promise<void>;
      error: (error: unknown) => void;
    },
  ): Promise<void>;

  unsubscribe(instance: string): void;

  shutdown(): Promise<void>;
}

export declare function fetchJSON<V extends Json>(
  url: string,
  method?: "POST" | "GET" | "PUT" | "PATCH" | "HEAD" | "DELETE",
  options?: {
    headers?: { [header: string]: string };
    body?: Json;
    timeout?: number;
  },
): Promise<[V | null, Headers]>;

export declare class Sum implements Reducer<number, number> {
  initial: number;
  add: (accum: number) => number;
  remove: (accum: number) => Nullable<number>;
}

export declare class Min implements Reducer<number, number> {
  initial: number;
  add: (accum: number) => number;
  remove: (accum: number) => Nullable<number>;
}

export declare class Max implements Reducer<number, number> {
  initial: number;
  add: (accum: number) => number;
  remove: (accum: number) => Nullable<number>;
}

export declare class Count<T extends Json> implements Reducer<T, number> {
  initial: number;
  add: (accum: number) => number;
  remove: (accum: number) => Nullable<number>;
}

export type Entrypoint = {
  host: string;
  streaming_port: number;
  control_port: number;
  secured?: boolean;
};

export declare class SkipServiceBroker {
  private readonly entrypoint: string;
  private timeout?: number;

  constructor(entrypoint?: Entrypoint, timeout?: number);

  getAll<K extends Json, V extends Json>(
    resource: string,
    params: Json,
  ): Promise<Entry<K, V>[]>;

  getArray<K extends Json, V extends Json>(
    resource: string,
    params: Json,
    key: K,
  ): Promise<V[]>;

  getUnique<K extends Json, V extends Json>(
    resource: string,
    params: Json,
    key: K,
  ): Promise<V>;

  update<K extends Json, V extends Json>(
    collection: string,
    entries: Entry<K, V>[],
  ): Promise<void>;

  deleteKey<K extends Json>(collection: string, key: K): Promise<void>;

  getStreamUUID(resource: string, params?: Json): Promise<string>;

  deleteUUID(uuid: string): Promise<void>;
}
