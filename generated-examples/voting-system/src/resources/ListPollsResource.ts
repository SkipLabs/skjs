import { FilterPollByStatusMapper } from "../mappers/FilterPollByStatusMapper.js";
import type {
  Poll_skip_id_,
  Poll_skip_value_,
  PollStatus,
  ListPollsParams,
  Poll,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListPollsResourceInputs extends SharedCollections {
  readonly polls: EagerCollection<Poll_skip_id_, Poll_skip_value_>;
}

export class ListPollsResource implements Resource<ListPollsResourceInputs> {
  private readonly status: PollStatus;

  constructor(params: ListPollsParams) {
    this.status = params.status;
  }

  instantiate(
    inputs: ListPollsResourceInputs,
    _context: Context,
  ): EagerCollection<Poll_skip_id_, Poll_skip_value_> {
    return inputs.polls.map(FilterPollByStatusMapper, this.status);
  }
}
