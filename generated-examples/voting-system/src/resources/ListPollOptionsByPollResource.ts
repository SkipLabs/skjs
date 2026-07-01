import type { Poll_skip_id_, PollOption, Poll } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface ListPollOptionsByPollResourceInputs extends SharedCollections {
  readonly optionsByPoll: EagerCollection<Poll_skip_id_, PollOption>;
}

export class ListPollOptionsByPollResource implements Resource<ListPollOptionsByPollResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: ListPollOptionsByPollResourceInputs,
    _context: Context,
  ): EagerCollection<Poll_skip_id_, PollOption> {
    return inputs.optionsByPoll;
  }
}
