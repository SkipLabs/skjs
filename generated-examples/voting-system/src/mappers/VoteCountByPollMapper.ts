import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  VoteKey,
  VoteStored,
  Poll_skip_id_,
  VoteCountValue,
  Poll,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each vote entry, emit one output pair whose key is sourced from the entry's key pollId field, paired with the literal value one. The original userId component of the key is dropped because the consumer aggregates total votes per poll and does not need voter identity; optionId in the value is dropped because the count is per-poll, not per-option.
export class VoteCountByPollMapper implements Mapper<
  VoteKey,
  VoteStored,
  Poll_skip_id_,
  VoteCountValue
> {
  mapEntry(
    key: VoteKey,
    values: Values<VoteStored>,
    context: Context,
  ): Iterable<[Poll_skip_id_, VoteCountValue]> {
    // > body
    const emits: [Poll_skip_id_, VoteCountValue][] = [];
    for (const _ of values.toArray()) {
      emits.push([key.pollId, 1]);
    }
    return emits;
    // < body
  }
}
