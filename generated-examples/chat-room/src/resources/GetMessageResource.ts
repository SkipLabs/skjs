import type {
  Message_skip_id_,
  Message_skip_value_,
  Message,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetMessageResourceInputs extends SharedCollections {
  readonly messages: EagerCollection<Message_skip_id_, Message_skip_value_>;
}

export class GetMessageResource implements Resource<GetMessageResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: GetMessageResourceInputs,
    _context: Context,
  ): EagerCollection<Message_skip_id_, Message_skip_value_> {
    return inputs.messages;
  }
}
