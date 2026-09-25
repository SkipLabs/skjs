// SkipService's `externalServices` is a readonly optional field: a service
// may lack it, so its read is not the dictionary alone.
import type { AnySkipService, ExternalService } from "@skipruntime/core";
export function externals(service: AnySkipService): {
  readonly [name: string]: ExternalService;
} {
  return service.externalServices;
}
