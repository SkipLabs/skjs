import type { ComponentIdKey, Heartbeat } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListHeartbeatsResourceInputs extends SharedCollections {
  readonly heartbeatsByComponent: EagerCollection<ComponentIdKey, Heartbeat>;
}

export class ListHeartbeatsResource implements Resource<ListHeartbeatsResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: ListHeartbeatsResourceInputs,
    _context: Context,
  ): EagerCollection<ComponentIdKey, Heartbeat> {
    return inputs.heartbeatsByComponent;
  }
}
