import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Poll_skip_id_,
  PollStored,
  Poll_skip_value_,
  PollOption,
  Poll,
} from "../types.js";
import type {
  Context,
  Mapper,
  Values,
  EagerCollection,
} from "@skipruntime/core";

// For each poll entry, consult optionsByPoll for the PollOption values indexed by the entry's key (the pollId). Sort the consulted options by their optionIndex field, ascending. Emit one output pair whose key is the entry's key and whose value lists every required field of Poll explicitly: ownerId sourced from the entry's value's ownerId field; question sourced from the entry's value's question field; options sourced from the sorted array of consulted PollOption values; closed sourced from the entry's value's closed field; createdAt sourced from the entry's value's createdAt field. The id field of Poll is recomposed from the entry's key at the api method boundary, not in the mapper output value.
export class AssemblePollMapper implements Mapper<
  Poll_skip_id_,
  PollStored,
  Poll_skip_id_,
  Poll_skip_value_
> {
  constructor(
    private optionsByPoll: EagerCollection<Poll_skip_id_, PollOption>,
  ) {}

  mapEntry(
    key: Poll_skip_id_,
    values: Values<PollStored>,
    context: Context,
  ): Iterable<[Poll_skip_id_, Poll_skip_value_]> {
    // > body
    const stored = values.toArray()[0];
    if (stored === undefined) return [];
    const options = this.optionsByPoll
      .getArray(key)
      .slice()
      .sort((a, b) => a.optionIndex - b.optionIndex);
    const out: Poll_skip_value_ = {
      ownerId: stored.ownerId,
      question: stored.question,
      options,
      closed: stored.closed,
      createdAt: stored.createdAt,
    };
    return [[key, out]];
    // < body
  }
}
