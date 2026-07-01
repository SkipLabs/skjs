import { AssemblePollMapper } from "../mappers/AssemblePollMapper.js";
import { PollOptionByPollMapper } from "../mappers/PollOptionByPollMapper.js";
import type {
  PollOption_skip_id_,
  PollOption_skip_value_,
  Poll_skip_id_,
  PollStored,
  Poll_skip_value_,
  PollOption,
  Poll,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetPollResourceInputs extends SharedCollections {
  readonly pollOptions: EagerCollection<
    PollOption_skip_id_,
    PollOption_skip_value_
  >;
  readonly polls: EagerCollection<Poll_skip_id_, PollStored>;
}

export class GetPollResource implements Resource<GetPollResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: GetPollResourceInputs,
    _context: Context,
  ): EagerCollection<Poll_skip_id_, Poll_skip_value_> {
    const optionsByPoll = inputs.pollOptions.map(PollOptionByPollMapper);
    return inputs.polls.map(AssemblePollMapper, optionsByPoll);
  }
}
