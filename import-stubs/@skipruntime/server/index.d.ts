import type {
  NamedInputDefinitions,
  NamedEagerCollections,
  SharedCollections,
  SkipService,
} from "@skipruntime/core";

export function runService<
  InputDefs extends NamedInputDefinitions,
  Inputs extends NamedEagerCollections,
  ResourceInputs extends SharedCollections,
>(
  service: SkipService<InputDefs, Inputs, ResourceInputs>,
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
