import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  PollOptionKey,
  PollOptionStored,
  Poll_skip_id_,
  PollOption,
  VoteCountValue,
  Poll,
} from "../types.js";
import type {
  Context,
  Mapper,
  Values,
  EagerCollection,
} from "@skipruntime/core";

// For each poll-option entry, consult voteCountByOption for the counts indexed by a composite key sourced from the entry's key (pollId and optionId). Take the first consulted value if present; otherwise default to zero. Emit one output pair whose key is sourced from the entry's key pollId field, and whose value is a PollOption listing every required field explicitly: pollId sourced from the entry's key pollId field; optionId sourced from the entry's key optionId field; label sourced from the entry's value label field; voteCount sourced from the resolved count (zero when no votes).
export class PollOptionByPollMapper implements Mapper<
  PollOptionKey,
  PollOptionStored,
  Poll_skip_id_,
  PollOption
> {
  constructor(
    private voteCountByOption: EagerCollection<PollOptionKey, VoteCountValue>,
  ) {}

  mapEntry(
    key: PollOptionKey,
    values: Values<PollOptionStored>,
    context: Context,
  ): Iterable<[Poll_skip_id_, PollOption]> {
    // > body
    const emits: [Poll_skip_id_, PollOption][] = [];
    for (const value of values.toArray()) {
      const counts = this.voteCountByOption.getArray(key);
      const voteCount = counts[0] ?? 0;
      const option: PollOption = {
        pollId: key.pollId,
        optionId: key.optionId,
        label: value.label,
        voteCount,
      };
      emits.push([key.pollId, option]);
    }
    return emits;
    // < body
  }
}
