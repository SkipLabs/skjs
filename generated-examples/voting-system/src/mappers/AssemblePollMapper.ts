import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Poll_skip_id_,
  PollStored,
  Poll_skip_value_,
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

// For each poll entry, consult optionsByPoll for the PollOption values indexed by the entry's key to obtain every option belonging to this poll. Consult totalVotesByPoll for the counts indexed by the entry's key; take the first consulted value if present, otherwise default to zero. Emit one output pair whose key is the entry's key and whose value lists every required field of Poll explicitly: id sourced from the entry's key; ownerId sourced from the entry's value ownerId field; question sourced from the entry's value question field; status sourced from the entry's value status field; options sourced from the consulted PollOption values (empty array when none); totalVotes sourced from the resolved count (zero when no votes); createdAt sourced from the entry's value createdAt field. Optional field closedAt: present when the entry's value has a closedAt field, sourced from that field; absent otherwise.
export class AssemblePollMapper implements Mapper<
  Poll_skip_id_,
  PollStored,
  Poll_skip_id_,
  Poll_skip_value_
> {
  constructor(
    private optionsByPoll: EagerCollection<Poll_skip_id_, PollOption>,
    private totalVotesByPoll: EagerCollection<Poll_skip_id_, VoteCountValue>,
  ) {}

  mapEntry(
    key: Poll_skip_id_,
    values: Values<PollStored>,
    context: Context,
  ): Iterable<[Poll_skip_id_, Poll_skip_value_]> {
    // > body
    const options = this.optionsByPoll.getArray(key);
    const totalVotesArr = this.totalVotesByPoll.getArray(key);
    const totalVotes = totalVotesArr[0] ?? 0;
    let stored: PollStored | undefined;
    for (const v of values) {
      stored = v;
      break;
    }
    if (stored === undefined) return [];
    const optionsArr: PollOption[] = [];
    for (const o of options) optionsArr.push(o);
    const out: Poll_skip_value_ = {
      ownerId: stored.ownerId,
      question: stored.question,
      status: stored.status,
      options: optionsArr,
      totalVotes,
      createdAt: stored.createdAt,
      ...(stored.closedAt !== undefined && { closedAt: stored.closedAt }),
    };
    return [[key, out]];
    // < body
  }
}
