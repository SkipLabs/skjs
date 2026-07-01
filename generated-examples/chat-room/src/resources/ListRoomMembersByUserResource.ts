import type { User_skip_id_, RoomMember, User } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface ListRoomMembersByUserResourceInputs extends SharedCollections {
  readonly roomMembersByUser: EagerCollection<User_skip_id_, RoomMember>;
}

export class ListRoomMembersByUserResource implements Resource<ListRoomMembersByUserResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: ListRoomMembersByUserResourceInputs,
    _context: Context,
  ): EagerCollection<User_skip_id_, RoomMember> {
    return inputs.roomMembersByUser;
  }
}
