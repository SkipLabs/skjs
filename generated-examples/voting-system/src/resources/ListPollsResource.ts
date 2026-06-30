import { AssemblePollMapper } from "../mappers/AssemblePollMapper.js";
import { FilterPollsByOwnerMapper } from "../mappers/FilterPollsByOwnerMapper.js";
import { PollOptionByPollMapper } from "../mappers/PollOptionByPollMapper.js";
import type {
  PollOption_skip_id_,
  PollOption_skip_value_,
  Poll_skip_id_,
  PollStored,
  Poll_skip_value_,
  ListPollsParams,
  PollOption,
  Poll,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListPollsResourceInputs extends SharedCollections {
  readonly pollOptions: EagerCollection<
    PollOption_skip_id_,
    PollOption_skip_value_
  >;
  readonly polls: EagerCollection<Poll_skip_id_, PollStored>;
}

export class ListPollsResource implements Resource<ListPollsResourceInputs> {
  private readonly ownerId: string | null;

  constructor(params: ListPollsParams) {
    this.ownerId = params.ownerId ?? null;
  }

  instantiate(
    inputs: ListPollsResourceInputs,
    _context: Context,
  ): EagerCollection<Poll_skip_id_, Poll_skip_value_> {
    const optionsByPoll = inputs.pollOptions.map(PollOptionByPollMapper);
    const assembledPolls = inputs.polls.map(AssemblePollMapper, optionsByPoll);
    return assembledPolls.map(FilterPollsByOwnerMapper, this.ownerId);
  }
}
