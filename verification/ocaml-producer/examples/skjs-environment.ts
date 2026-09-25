// SKJS's test environment: a bare specifier resolves in its import stubs,
// `__SKJS_show` is a host function taking any value, `process` is SKJS's stub
// of Node's, and `Closed<T>` is read as `T`.
import { functionFromStubs } from "for-tests";

type Point = Closed<{ x: number }>;

function measured(p: Point): number {
  __SKJS_show(p.x, "number");
  return functionFromStubs("p") + p.x;
}

export function onShutdown(close: () => Promise<void>): void {
  const shutdown = async (): Promise<void> => {
    await close();
  };
  process.on("SIGTERM", shutdown);
}

const origin: Point = { x: 0 };
__SKJS_show(measured(origin));
