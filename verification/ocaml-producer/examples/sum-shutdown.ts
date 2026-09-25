// sum.ts, main, apart from runService: an async closure registered with
// Node's `process.on` for each signal. `on`'s last overload offers the
// listener `(...args: unknown[]) => void`, at which the closure is created.
interface Server {
  close(): Promise<void>;
}
export function register(server: Server): void {
  const shutdown = async (): Promise<void> => {
    await server.close();
  };
  for (const sig of ["SIGTERM", "SIGINT"]) process.on(sig, shutdown);
}
