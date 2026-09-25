// sum.ts, main: async/await, a module constant read from `process`, and a
// `for...of` over an array literal.
import { runService } from "@skipruntime/server";
import type { SkipService } from "@skipruntime/core";
const platform: "wasm" | "native" =
  process.env["SKIP_PLATFORM"] === "native" ? "native" : "wasm";
export async function main(service: SkipService): Promise<void> {
  const server = await runService(service, {
    control_port: 3588,
    streaming_port: 3587,
    platform,
  });
  const shutdown = async (): Promise<void> => {
    await server.close();
  };
  for (const sig of ["SIGTERM", "SIGINT"]) process.on(sig, shutdown);
}
