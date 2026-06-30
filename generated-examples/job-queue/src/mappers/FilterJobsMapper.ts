import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { Job_skip_id_, Job_skip_value_, Job } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each job entry, emit the entry unchanged when ALL of the following hold: (the status param is absent OR the entry's status field equals the status param literally) AND (the ownerId param is absent OR the entry's ownerId field equals the ownerId param literally) AND (the queueName param is absent OR the entry's queueName field equals the queueName param literally). Otherwise emit nothing.
export class FilterJobsMapper implements Mapper<
  Job_skip_id_,
  Job_skip_value_,
  Job_skip_id_,
  Job_skip_value_
> {
  constructor(
    private status: string | null,
    private ownerId: string | null,
    private queueName: string | null,
  ) {}

  mapEntry(
    key: Job_skip_id_,
    values: Values<Job_skip_value_>,
    context: Context,
  ): Iterable<[Job_skip_id_, Job_skip_value_]> {
    // > body
    const emits: [Job_skip_id_, Job_skip_value_][] = [];
    for (const value of values.toArray()) {
      if (this.status !== null && value.status !== this.status) continue;
      if (this.ownerId !== null && value.ownerId !== this.ownerId) continue;
      if (this.queueName !== null && value.queueName !== this.queueName)
        continue;
      emits.push([key, value]);
    }
    return emits;
    // < body
  }
}
