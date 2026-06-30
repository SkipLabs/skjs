import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Vote_skip_id_,
  Vote_skip_value_,
  Poll_skip_id_,
  Vote,
  Poll,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each vote entry, emit one output pair whose key is sourced from the entry's key's pollId field, and whose value lists every required field of Vote explicitly: pollId sourced from the entry's key's pollId field; voterId sourced from the entry's key's voterId field; optionIndex sourced from the entry's value's optionIndex field; castAt sourced from the entry's value's castAt field. The original voterId from the key is re-injected into the value so downstream consumers can reconstruct full Vote entities under the new key keyed by pollId alone.
export class VoteByPollMapper implements Mapper<
  Vote_skip_id_,
  Vote_skip_value_,
  Poll_skip_id_,
  Vote
> {
  mapEntry(
    key: Vote_skip_id_,
    values: Values<Vote_skip_value_>,
    context: Context,
  ): Iterable<[Poll_skip_id_, Vote]> {
    // > body
    const emits: [Poll_skip_id_, Vote][] = [];
    for (const value of values.toArray()) {
      emits.push([
        key.pollId,
        {
          pollId: key.pollId,
          voterId: key.voterId,
          optionIndex: value.optionIndex,
          castAt: value.castAt,
        },
      ]);
    }
    return emits;
    // < body
  }
}
