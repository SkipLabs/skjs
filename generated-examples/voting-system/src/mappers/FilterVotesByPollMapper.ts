import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { Vote_skip_id_, Vote_skip_value_, Vote } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each vote entry, emit the entry unchanged when the entry's key's pollId field equals the pollId param. Otherwise emit nothing.
export class FilterVotesByPollMapper implements Mapper<
  Vote_skip_id_,
  Vote_skip_value_,
  Vote_skip_id_,
  Vote_skip_value_
> {
  constructor(private pollId: string) {}

  mapEntry(
    key: Vote_skip_id_,
    values: Values<Vote_skip_value_>,
    context: Context,
  ): Iterable<[Vote_skip_id_, Vote_skip_value_]> {
    // > body
    const emits: [Vote_skip_id_, Vote_skip_value_][] = [];
    if (key.pollId === this.pollId) {
      for (const value of values.toArray()) {
        emits.push([key, value]);
      }
    }
    return emits;
    // < body
  }
}
