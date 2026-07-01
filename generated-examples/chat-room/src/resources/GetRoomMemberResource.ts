import type {
  RoomMemberCompositeKey,
  RoomMember_skip_value_,
  RoomMember,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetRoomMemberResourceInputs extends SharedCollections {
  readonly roomMembers: EagerCollection<
    RoomMemberCompositeKey,
    RoomMember_skip_value_
  >;
}

export class GetRoomMemberResource implements Resource<GetRoomMemberResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetRoomMemberResourceInputs,
    _context: Context,
  ): EagerCollection<RoomMemberCompositeKey, RoomMember_skip_value_> {
    return inputs.roomMembers;
  }
}
