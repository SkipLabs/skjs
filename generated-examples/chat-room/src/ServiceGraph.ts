import type {
  RoomMembershipKey,
  RoomMembership_skip_value_,
  RoomMembership,
  Message_skip_id_,
  Message,
  Message_skip_value_,
  Room_skip_id_,
  Room,
  Room_skip_value_,
  User_skip_id_,
  User,
  User_skip_value_,
} from "./types.js";
import type {
  EagerCollection,
  Context,
  NamedEagerCollections,
  SharedCollections,
} from "@skipruntime/core";

export interface InputCollections extends NamedEagerCollections {
  readonly memberships: EagerCollection<
    RoomMembershipKey,
    RoomMembership_skip_value_
  >;
  readonly messages: EagerCollection<Message_skip_id_, Message_skip_value_>;
  readonly rooms: EagerCollection<Room_skip_id_, Room_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export interface GraphCollections extends SharedCollections {
  readonly memberships: EagerCollection<
    RoomMembershipKey,
    RoomMembership_skip_value_
  >;
  readonly messages: EagerCollection<Message_skip_id_, Message_skip_value_>;
  readonly rooms: EagerCollection<Room_skip_id_, Room_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const output_memberships = inputs.memberships;
  const output_messages = inputs.messages;
  const output_rooms = inputs.rooms;
  const output_users = inputs.users;
  return {
    memberships: output_memberships,
    messages: output_messages,
    rooms: output_rooms,
    users: output_users,
  };
}
