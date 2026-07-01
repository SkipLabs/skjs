import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  OptionTally,
  Poll_skip_id_,
  Poll_skip_value_,
  PollResults,
  Vote,
  Poll,
} from "../types.js";
import type {
  Context,
  Mapper,
  Values,
  EagerCollection,
} from "@skipruntime/core";

// For each poll entry, when the entry's key does not equal the pollId param, emit nothing. Otherwise, consult votesByPoll for the Vote values indexed by the pollId param to obtain all votes cast on this poll. For each option in the entry's value's options array, in optionIndex ascending order, build a tally entry whose optionIndex is sourced from the option's optionIndex field; text is sourced from the option's text field; votes is sourced from the consulted votes filtered to those whose optionIndex equals this option's optionIndex; count is the length of that filtered votes array. Emit one output pair whose key is the literal-zero and whose value lists every required field of PollResults explicitly: pollId sourced from the pollId param; votes sourced from the full consulted votes array; totalVotes is the length of the consulted votes array; tallies sourced from the array of tally entries built above.
export class PollResultsMapper implements Mapper<
  Poll_skip_id_,
  Poll_skip_value_,
  0,
  PollResults
> {
  constructor(
    private pollId: string,
    private votesByPoll: EagerCollection<Poll_skip_id_, Vote>,
  ) {}

  mapEntry(
    key: Poll_skip_id_,
    values: Values<Poll_skip_value_>,
    context: Context,
  ): Iterable<[0, PollResults]> {
    // > body
    if (key !== this.pollId) return [];
    const consultedVotes = this.votesByPoll.getArray(this.pollId);
    const emits: [0, PollResults][] = [];
    for (const value of values.toArray()) {
      const sortedOptions = value.options
        .slice()
        .sort((a, b) => a.optionIndex - b.optionIndex);
      const tallies: OptionTally[] = [];
      for (const option of sortedOptions) {
        const filteredVotes: Vote[] = [];
        for (const v of consultedVotes) {
          if (v.optionIndex === option.optionIndex) filteredVotes.push(v);
        }
        tallies.push({
          optionIndex: option.optionIndex,
          text: option.text,
          votes: filteredVotes,
          count: filteredVotes.length,
        });
      }
      const result: PollResults = {
        pollId: this.pollId,
        votes: consultedVotes,
        totalVotes: consultedVotes.length,
        tallies,
      };
      emits.push([0, result]);
    }
    return emits;
    // < body
  }
}
