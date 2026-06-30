import type { Vote_skip_id_, Vote_skip_value_, Vote } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetVoteResourceInputs extends SharedCollections {
  readonly votes: EagerCollection<Vote_skip_id_, Vote_skip_value_>;
}

export class GetVoteResource implements Resource<GetVoteResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: GetVoteResourceInputs,
    _context: Context,
  ): EagerCollection<Vote_skip_id_, Vote_skip_value_> {
    return inputs.votes;
  }
}
