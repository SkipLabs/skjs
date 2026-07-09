import type { Poll_skip_id_, PollStored, Poll } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetPollStoredResourceInputs extends SharedCollections {
  readonly pollsStored: EagerCollection<Poll_skip_id_, PollStored>;
}

export class GetPollStoredResource implements Resource<GetPollStoredResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetPollStoredResourceInputs,
    _context: Context,
  ): EagerCollection<Poll_skip_id_, PollStored> {
    return inputs.pollsStored;
  }
}
