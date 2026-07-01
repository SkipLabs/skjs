import { MessageByChannelMapper } from "../mappers/MessageByChannelMapper.js";
import type {
  Message_skip_id_,
  Message_skip_value_,
  Channel_skip_id_,
  Message,
  Channel,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface ListChannelMessagesResourceInputs extends SharedCollections {
  readonly messages: EagerCollection<Message_skip_id_, Message_skip_value_>;
}

export class ListChannelMessagesResource implements Resource<ListChannelMessagesResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: ListChannelMessagesResourceInputs,
    _context: Context,
  ): EagerCollection<Channel_skip_id_, Message> {
    const messagesByChannel = inputs.messages.map(MessageByChannelMapper);
    return messagesByChannel;
  }
}
