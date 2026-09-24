// Runtime APIs a Skip service client uses beyond generated code: a mapper
// reading the only value of a key with `Values.getUnique`, as the Skip
// Runtime's `sum` example does, and a signal handler registered with
// `process.on` for shutdown.

import type { Mapper, Values } from "@skipruntime/core";

export class FirstValue implements Mapper<string, number, string, number> {
  mapEntry(key: string, values: Values<number>): Iterable<[string, number]> {
    return [[key, values.getUnique()]];
  }
}

export class FirstOrZero implements Mapper<string, number, string, number> {
  mapEntry(key: string, values: Values<number>): Iterable<[string, number]> {
    return [[key, values.getUnique({ ifMany: 0 })]];
  }
}

export function onShutdown(close: () => Promise<void>): void {
  const shutdown = async (): Promise<void> => {
    await close();
  };
  for (const sig of ["SIGTERM", "SIGINT"]) process.on(sig, shutdown);
}
