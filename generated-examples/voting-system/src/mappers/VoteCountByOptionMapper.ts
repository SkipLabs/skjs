import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  VoteKey,
  VoteStored,
  PollOptionKey,
  VoteCountValue,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each vote entry, emit one output pair whose key is a composite object with pollId sourced from the entry's key pollId field and optionId sourced from the entry's value optionId field, paired with the literal value one. The original userId component of the key is dropped because the consumer aggregates counts per (pollId, optionId) and does not need voter identity.
export class VoteCountByOptionMapper implements Mapper<
  VoteKey,
  VoteStored,
  PollOptionKey,
  VoteCountValue
> {
  mapEntry(
    key: VoteKey,
    values: Values<VoteStored>,
    context: Context,
  ): Iterable<[PollOptionKey, VoteCountValue]> {
    // > body
    const emits: [PollOptionKey, VoteCountValue][] = [];
    for (const value of values.toArray()) {
      emits.push([{ pollId: key.pollId, optionId: value.optionId }, 1]);
    }
    return emits;
    // < body
  }
}
