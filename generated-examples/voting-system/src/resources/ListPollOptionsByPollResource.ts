import { PollOptionByPollMapper } from "../mappers/PollOptionByPollMapper.js";
import type {
  PollOption_skip_id_,
  PollOption_skip_value_,
  Poll_skip_id_,
  PollOption,
  Poll,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListPollOptionsByPollResourceInputs extends SharedCollections {
  readonly pollOptions: EagerCollection<
    PollOption_skip_id_,
    PollOption_skip_value_
  >;
}

export class ListPollOptionsByPollResource implements Resource<ListPollOptionsByPollResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: ListPollOptionsByPollResourceInputs,
    _context: Context,
  ): EagerCollection<Poll_skip_id_, PollOption> {
    const optionsByPoll = inputs.pollOptions.map(PollOptionByPollMapper);
    return optionsByPoll;
  }
}
