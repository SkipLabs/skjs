import type { Poll_skip_id_, Vote, Poll } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface ListVotesByPollResourceInputs extends SharedCollections {
  readonly votesByPoll: EagerCollection<Poll_skip_id_, Vote>;
}

export class ListVotesByPollResource implements Resource<ListVotesByPollResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: ListVotesByPollResourceInputs,
    _context: Context,
  ): EagerCollection<Poll_skip_id_, Vote> {
    return inputs.votesByPoll;
  }
}
