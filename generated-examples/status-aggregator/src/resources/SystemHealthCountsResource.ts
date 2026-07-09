import type { ComponentStatusKey, ComponentStatusCount } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface SystemHealthCountsResourceInputs extends SharedCollections {
  readonly componentStatusCounts: EagerCollection<
    ComponentStatusKey,
    ComponentStatusCount
  >;
}

export class SystemHealthCountsResource implements Resource<SystemHealthCountsResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: SystemHealthCountsResourceInputs,
    _context: Context,
  ): EagerCollection<ComponentStatusKey, ComponentStatusCount> {
    return inputs.componentStatusCounts;
  }
}
