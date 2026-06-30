import { FilterVotesByPollMapper } from "../mappers/FilterVotesByPollMapper.js";
import type {
  Vote_skip_id_,
  Vote_skip_value_,
  ListVotesForPollParams,
  Vote,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListVotesForPollResourceInputs extends SharedCollections {
  readonly votes: EagerCollection<Vote_skip_id_, Vote_skip_value_>;
}

export class ListVotesForPollResource implements Resource<ListVotesForPollResourceInputs> {
  private readonly pollId: string;

  constructor(params: ListVotesForPollParams) {
    this.pollId = params.pollId;
  }

  instantiate(
    inputs: ListVotesForPollResourceInputs,
    _context: Context,
  ): EagerCollection<Vote_skip_id_, Vote_skip_value_> {
    return inputs.votes.map(FilterVotesByPollMapper, this.pollId);
  }
}
