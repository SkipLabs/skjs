import { MessageByRoomMapper } from "./mappers/MessageByRoomMapper.js";
import { MessageByRoomOrderedMapper } from "./mappers/MessageByRoomOrderedMapper.js";
import { RoomMemberByRoomFullMapper } from "./mappers/RoomMemberByRoomFullMapper.js";
import { RoomMemberByUserMapper } from "./mappers/RoomMemberByUserMapper.js";
import type {
  Message_skip_id_,
  Message,
  Message_skip_value_,
  RoomMemberCompositeKey,
  RoomMember_skip_value_,
  RoomMember,
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
  readonly messages: EagerCollection<Message_skip_id_, Message_skip_value_>;
  readonly roomMembers: EagerCollection<
    RoomMemberCompositeKey,
    RoomMember_skip_value_
  >;
  readonly rooms: EagerCollection<Room_skip_id_, Room_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export interface GraphCollections extends SharedCollections {
  readonly messages: EagerCollection<Message_skip_id_, Message_skip_value_>;
  readonly messagesByRoom: EagerCollection<Room_skip_id_, Message>;
  readonly roomMembers: EagerCollection<
    RoomMemberCompositeKey,
    RoomMember_skip_value_
  >;
  readonly roomMembersByRoom: EagerCollection<Room_skip_id_, RoomMember>;
  readonly roomMembersByUser: EagerCollection<User_skip_id_, RoomMember>;
  readonly rooms: EagerCollection<Room_skip_id_, Room_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const messagesOrdered = inputs.messages.map(MessageByRoomOrderedMapper);
  const messagesByRoom = messagesOrdered.map(MessageByRoomMapper);
  const output_messages = inputs.messages;
  const output_messagesByRoom = messagesByRoom;
  const output_roomMembers = inputs.roomMembers;
  const roomMembersByRoom = inputs.roomMembers.map(RoomMemberByRoomFullMapper);
  const output_roomMembersByRoom = roomMembersByRoom;
  const roomMembersByUser = inputs.roomMembers.map(RoomMemberByUserMapper);
  const output_roomMembersByUser = roomMembersByUser;
  const output_rooms = inputs.rooms;
  const output_users = inputs.users;
  return {
    messages: output_messages,
    messagesByRoom: output_messagesByRoom,
    roomMembers: output_roomMembers,
    roomMembersByRoom: output_roomMembersByRoom,
    roomMembersByUser: output_roomMembersByUser,
    rooms: output_rooms,
    users: output_users,
  };
}
