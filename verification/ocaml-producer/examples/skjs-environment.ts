// SKJS's test environment: a bare specifier resolves in its import stubs,
// `__SKJS_show` is a host function taking any value, `process` and `console`
// are SKJS's stubs of Node's, `Closed<T>` is read as `T`, and no DOM global
// (`Event`) collides with the test's own names.
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

type Event = { kind: string };
function logged(e: Event): void {
  console.log("event", e.kind);
}

const origin: Point = { x: 0 };
__SKJS_show(measured(origin));
