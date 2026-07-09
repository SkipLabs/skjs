import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Poll_skip_id_,
  Poll_skip_value_,
  PollStatus,
  Poll,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each poll entry, emit the entry unchanged when the entry's value status field equals the status param. Otherwise emit nothing.
export class FilterPollByStatusMapper implements Mapper<
  Poll_skip_id_,
  Poll_skip_value_,
  Poll_skip_id_,
  Poll_skip_value_
> {
  constructor(private status: PollStatus) {}

  mapEntry(
    key: Poll_skip_id_,
    values: Values<Poll_skip_value_>,
    context: Context,
  ): Iterable<[Poll_skip_id_, Poll_skip_value_]> {
    // > body
    const emits: [Poll_skip_id_, Poll_skip_value_][] = [];
    for (const value of values.toArray()) {
      if (value.status === this.status) {
        emits.push([key, value]);
      }
    }
    return emits;
    // < body
  }
}
