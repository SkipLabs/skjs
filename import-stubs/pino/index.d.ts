export interface TransportBaseOptions {
  options?: { [opt: string]: unknown };
  // worker?: WorkerOptions & { autoEnd?: boolean}
}

export interface TransportSingleOptions extends TransportBaseOptions {
  target: string;
}

export type LoggerOptions = {
  transport?: TransportSingleOptions;
};

export type Level = "fatal" | "error" | "warn" | "info" | "debug" | "trace";

export type LevelWithSilent = Level | "silent";
