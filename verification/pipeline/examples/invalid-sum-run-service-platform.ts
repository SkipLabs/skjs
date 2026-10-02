// runService's `platform` is an optional field of "wasm" | "native": a field
// holding any string does not establish it.
import { runService, type SkipServer } from "@skipruntime/server";
import type { AnySkipService } from "@skipruntime/core";
export function start(
  service: AnySkipService,
  platform: string,
): Promise<SkipServer> {
  return runService(service, {
    control_port: 3588,
    streaming_port: 3587,
    platform,
    no_cors: false,
  });
}
