// sum.ts, runService: the service's type reaches SkipService's readonly
// optional `externalServices`, read here as present or undefined, and the
// options' type has optional fields.
import { runService } from "@skipruntime/server";
import type { AnySkipService, ExternalService } from "@skipruntime/core";
export async function start(
  service: AnySkipService,
  platform: "wasm" | "native",
): Promise<void> {
  await runService(service, {
    control_port: 3588,
    streaming_port: 3587,
    platform,
    no_cors: false,
  });
}
export function externals(
  service: AnySkipService,
): { readonly [name: string]: ExternalService } | undefined {
  return service.externalServices;
}
