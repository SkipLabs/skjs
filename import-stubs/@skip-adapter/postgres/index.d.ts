import type { Entry, ExternalService, Json } from "@skipruntime/core";

export declare class PostgresExternalService implements ExternalService {
  //   private client: pg.Client;
  //   private open_instances: Set<string>;

  isConnected(): boolean;

  constructor(db_config: {
    host: string;
    port: number;
    database: string;
    user: string;
    password: string;
  });

  subscribe(
    instance: string,
    resource: string,
    params: {
      key: {
        col: string;
        type: PostgresPKey;
      };
      syncHistoricData?: boolean;
    },
    callbacks: {
      update: (updates: Entry<Json, Json>[], isInit: boolean) => Promise<void>;
      error: (error: Json) => void;
    },
  ): Promise<void>;

  unsubscribe(instance: string): void;

  shutdown(): Promise<void>;
}

export type PostgresPKey =
  | "TEXT"
  | "SERIAL"
  | "SERIAL2"
  | "SERIAL4"
  | "SERIAL8"
  | "BIGSERIAL"
  | "SMALLSERIAL"
  | "INTEGER"
  | "INT"
  | "INT2"
  | "INT4"
  | "INT8"
  | "BIGINT"
  | "SMALLINT";
