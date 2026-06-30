import type { Poll_skip_id_, PollStored, Poll } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetPollStoredResourceInputs extends SharedCollections {
  readonly polls: EagerCollection<Poll_skip_id_, PollStored>;
}

export class GetPollStoredResource implements Resource<GetPollStoredResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: GetPollStoredResourceInputs,
    _context: Context,
  ): EagerCollection<Poll_skip_id_, PollStored> {
    return inputs.polls;
  }
}
