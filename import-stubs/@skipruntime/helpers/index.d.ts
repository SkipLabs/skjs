import type { Json, Entry } from "@skipruntime/core";

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
