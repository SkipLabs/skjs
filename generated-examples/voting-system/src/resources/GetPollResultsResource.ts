import { AssemblePollMapper } from "../mappers/AssemblePollMapper.js";
import { PollOptionByPollMapper } from "../mappers/PollOptionByPollMapper.js";
import { PollResultsMapper } from "../mappers/PollResultsMapper.js";
import { VoteByPollMapper } from "../mappers/VoteByPollMapper.js";
import type {
  PollOption_skip_id_,
  PollOption_skip_value_,
  Poll_skip_id_,
  PollStored,
  Vote_skip_id_,
  Vote_skip_value_,
  PollResults,
  GetPollResultsParams,
  PollOption,
  Poll,
  Vote,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetPollResultsResourceInputs extends SharedCollections {
  readonly pollOptions: EagerCollection<
    PollOption_skip_id_,
    PollOption_skip_value_
  >;
  readonly polls: EagerCollection<Poll_skip_id_, PollStored>;
  readonly votes: EagerCollection<Vote_skip_id_, Vote_skip_value_>;
}

export class GetPollResultsResource implements Resource<GetPollResultsResourceInputs> {
  private readonly pollId: string;

  constructor(params: GetPollResultsParams) {
    this.pollId = params.pollId;
  }

  instantiate(
    inputs: GetPollResultsResourceInputs,
    _context: Context,
  ): EagerCollection<0, PollResults> {
    const optionsByPoll = inputs.pollOptions.map(PollOptionByPollMapper);
    const assembledPolls = inputs.polls.map(AssemblePollMapper, optionsByPoll);
    const votesByPoll = inputs.votes.map(VoteByPollMapper);
    return assembledPolls.map(PollResultsMapper, this.pollId, votesByPoll);
  }
}
