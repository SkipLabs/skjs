import type {
  Channel_skip_id_,
  Channel_skip_value_,
  Channel,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetChannelResourceInputs extends SharedCollections {
  readonly channels: EagerCollection<Channel_skip_id_, Channel_skip_value_>;
}

export class GetChannelResource implements Resource<GetChannelResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetChannelResourceInputs,
    _context: Context,
  ): EagerCollection<Channel_skip_id_, Channel_skip_value_> {
    return inputs.channels;
  }
}
