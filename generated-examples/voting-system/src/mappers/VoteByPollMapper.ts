import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  VoteKey,
  VoteStored,
  Poll_skip_id_,
  Vote,
  Poll,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each vote entry, emit one output pair whose key is sourced from the entry's key pollId field, and whose value is a Vote listing every required field explicitly: pollId sourced from the entry's key pollId field; userId sourced from the entry's key userId field; optionId sourced from the entry's value optionId field; castAt sourced from the entry's value castAt field.
export class VoteByPollMapper implements Mapper<
  VoteKey,
  VoteStored,
  Poll_skip_id_,
  Vote
> {
  mapEntry(
    key: VoteKey,
    values: Values<VoteStored>,
    context: Context,
  ): Iterable<[Poll_skip_id_, Vote]> {
    // > body
    const emits: [Poll_skip_id_, Vote][] = [];
    for (const value of values.toArray()) {
      emits.push([
        key.pollId,
        {
          pollId: key.pollId,
          userId: key.userId,
          optionId: value.optionId,
          castAt: value.castAt,
        },
      ]);
    }
    return emits;
    // < body
  }
}
