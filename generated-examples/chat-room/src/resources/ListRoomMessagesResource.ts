import type { Room_skip_id_, Message, Room } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface ListRoomMessagesResourceInputs extends SharedCollections {
  readonly messagesByRoom: EagerCollection<Room_skip_id_, Message>;
}

export class ListRoomMessagesResource implements Resource<ListRoomMessagesResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: ListRoomMessagesResourceInputs,
    _context: Context,
  ): EagerCollection<Room_skip_id_, Message> {
    return inputs.messagesByRoom;
  }
}
