import type { NamedCollections, SkipService } from "@skipruntime/core";

export function runService<
  Inputs extends NamedCollections /* = NamedCollections */,
  ResourceInputs extends NamedCollections /* = NamedCollections */,
>(
  service: SkipService<Inputs, ResourceInputs>,
  options?: {
    streaming_port: number;
    control_port: number;
    platform?: "wasm" | "native";
    no_cors?: boolean;
  },
): Promise<SkipServer>;

export type SkipServer = {
  close: () => Promise<void>;
};
