import type { Poll_skip_id_, Poll_skip_value_, Poll } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetPollResourceInputs extends SharedCollections {
  readonly polls: EagerCollection<Poll_skip_id_, Poll_skip_value_>;
}

export class GetPollResource implements Resource<GetPollResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetPollResourceInputs,
    _context: Context,
  ): EagerCollection<Poll_skip_id_, Poll_skip_value_> {
    return inputs.polls;
  }
}
