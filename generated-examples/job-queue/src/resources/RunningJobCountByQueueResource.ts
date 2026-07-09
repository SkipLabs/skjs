import type { Queue_skip_id_, RunningJobCount, Queue } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface RunningJobCountByQueueResourceInputs extends SharedCollections {
  readonly runningCountByQueue: EagerCollection<
    Queue_skip_id_,
    RunningJobCount
  >;
}

export class RunningJobCountByQueueResource implements Resource<RunningJobCountByQueueResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: RunningJobCountByQueueResourceInputs,
    _context: Context,
  ): EagerCollection<Queue_skip_id_, RunningJobCount> {
    return inputs.runningCountByQueue;
  }
}
