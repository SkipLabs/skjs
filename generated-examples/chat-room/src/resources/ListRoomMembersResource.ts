import { MembershipByRoomMapper } from "../mappers/MembershipByRoomMapper.js";
import type {
  RoomMembershipKey,
  RoomMembership_skip_value_,
  Room_skip_id_,
  RoomMembership,
  Room,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListRoomMembersResourceInputs extends SharedCollections {
  readonly memberships: EagerCollection<
    RoomMembershipKey,
    RoomMembership_skip_value_
  >;
}

export class ListRoomMembersResource implements Resource<ListRoomMembersResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: ListRoomMembersResourceInputs,
    _context: Context,
  ): EagerCollection<Room_skip_id_, RoomMembership> {
    const membershipsByRoom = inputs.memberships.map(MembershipByRoomMapper);
    return membershipsByRoom;
  }
}
