import type { Room_skip_id_, RoomMember, Room } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface ListRoomMembersByRoomResourceInputs extends SharedCollections {
  readonly roomMembersByRoom: EagerCollection<Room_skip_id_, RoomMember>;
}

export class ListRoomMembersByRoomResource implements Resource<ListRoomMembersByRoomResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: ListRoomMembersByRoomResourceInputs,
    _context: Context,
  ): EagerCollection<Room_skip_id_, RoomMember> {
    return inputs.roomMembersByRoom;
  }
}
