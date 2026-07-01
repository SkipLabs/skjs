import type { VoteKey, VoteStored } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetVoteResourceInputs extends SharedCollections {
  readonly votes: EagerCollection<VoteKey, VoteStored>;
}

export class GetVoteResource implements Resource<GetVoteResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetVoteResourceInputs,
    _context: Context,
  ): EagerCollection<VoteKey, VoteStored> {
    return inputs.votes;
  }
}
