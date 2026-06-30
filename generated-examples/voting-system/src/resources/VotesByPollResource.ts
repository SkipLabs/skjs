import { VoteByPollMapper } from "../mappers/VoteByPollMapper.js";
import type {
  Vote_skip_id_,
  Vote_skip_value_,
  Poll_skip_id_,
  Vote,
  Poll,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface VotesByPollResourceInputs extends SharedCollections {
  readonly votes: EagerCollection<Vote_skip_id_, Vote_skip_value_>;
}

export class VotesByPollResource implements Resource<VotesByPollResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: VotesByPollResourceInputs,
    _context: Context,
  ): EagerCollection<Poll_skip_id_, Vote> {
    return inputs.votes.map(VoteByPollMapper);
  }
}
