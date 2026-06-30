import { MessageByRoomMapper } from "../mappers/MessageByRoomMapper.js";
import type {
  Message_skip_id_,
  Message_skip_value_,
  Room_skip_id_,
  Message,
  Room,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListRoomMessagesResourceInputs extends SharedCollections {
  readonly messages: EagerCollection<Message_skip_id_, Message_skip_value_>;
}

export class ListRoomMessagesResource implements Resource<ListRoomMessagesResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: ListRoomMessagesResourceInputs,
    _context: Context,
  ): EagerCollection<Room_skip_id_, Message> {
    const messagesByRoom = inputs.messages.map(MessageByRoomMapper);
    return messagesByRoom;
  }
}
