import { MessagesByChannelMapper } from "../mappers/MessagesByChannelMapper.js";
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
} from "@skipruntime/core";

export interface MessagesByChannelResourceInputs extends SharedCollections {
  readonly messages: EagerCollection<Message_skip_id_, Message_skip_value_>;
}

export class MessagesByChannelResource implements Resource<MessagesByChannelResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: MessagesByChannelResourceInputs,
    _context: Context,
  ): EagerCollection<Channel_skip_id_, Message> {
    const messagesByChannel = inputs.messages.map(MessagesByChannelMapper);
    return messagesByChannel;
  }
}
