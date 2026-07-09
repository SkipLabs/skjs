import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { Job_skip_id_, Job_skip_value_, Job } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each job entry, emit the entry unchanged when the entry's value's queueId field equals the queueId param AND (the status param is absent OR the entry's value's status field equals the status param). Otherwise emit nothing.
export class FilterJobByQueueAndStatusMapper implements Mapper<
  Job_skip_id_,
  Job_skip_value_,
  Job_skip_id_,
  Job_skip_value_
> {
  constructor(
    private queueId: string,
    private status: string | null,
  ) {}

  mapEntry(
    key: Job_skip_id_,
    values: Values<Job_skip_value_>,
    context: Context,
  ): Iterable<[Job_skip_id_, Job_skip_value_]> {
    // > body
    const emits: [Job_skip_id_, Job_skip_value_][] = [];
    for (const value of values.toArray()) {
      if (
        value.queueId === this.queueId &&
        (this.status === null || value.status === this.status)
      ) {
        emits.push([key, value]);
      }
    }
    return emits;
    // < body
  }
}
