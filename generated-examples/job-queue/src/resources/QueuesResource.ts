import type { Queue_skip_id_, Queue_skip_value_, Queue } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface QueuesResourceInputs extends SharedCollections {
  readonly queues: EagerCollection<Queue_skip_id_, Queue_skip_value_>;
}

export class QueuesResource implements Resource<QueuesResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: QueuesResourceInputs,
    _context: Context,
  ): EagerCollection<Queue_skip_id_, Queue_skip_value_> {
    return inputs.queues;
  }
}
