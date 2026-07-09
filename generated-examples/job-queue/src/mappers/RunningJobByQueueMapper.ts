import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Job_skip_id_,
  Job_skip_value_,
  Queue_skip_id_,
  RunningJobCount,
  Job,
  Queue,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each job entry, when the entry's value's status field equals the literal 'running', emit one output pair whose key is sourced from the entry's value's queueId field (the Queue primary key) and whose value is the literal one. Otherwise emit nothing. The original Job.id (the source entry's key) is dropped: this mapper feeds a per-queue running-count reducer (SumReducer over RunningJobCount) where source-job identity is not needed downstream — the consumer (RunningJobCountByQueueResource) serves only the aggregate count per queueId, not individual Job rows.
export class RunningJobByQueueMapper implements Mapper<
  Job_skip_id_,
  Job_skip_value_,
  Queue_skip_id_,
  RunningJobCount
> {
  mapEntry(
    key: Job_skip_id_,
    values: Values<Job_skip_value_>,
    context: Context,
  ): Iterable<[Queue_skip_id_, RunningJobCount]> {
    // > body
    const emits: [Queue_skip_id_, RunningJobCount][] = [];
    for (const value of values.toArray()) {
      if (value.status === "running") {
        emits.push([value.queueId, 1]);
      }
    }
    return emits;
    // < body
  }
}
