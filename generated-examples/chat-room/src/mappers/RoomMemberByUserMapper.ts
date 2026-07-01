import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  RoomMemberCompositeKey,
  RoomMember_skip_value_,
  User_skip_id_,
  RoomMember,
  User,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each room member entry, emit one output pair whose key is sourced from the entry's key userId field (the User primary key), paired with a full RoomMember record. The output value lists every required field of RoomMember explicitly: roomId sourced from the entry's key roomId field; userId sourced from the entry's key userId field; joinedAt sourced from the entry's value joinedAt field. The original userId component of the input key is encoded into the new key; the original roomId is re-injected into the value.
export class RoomMemberByUserMapper implements Mapper<
  RoomMemberCompositeKey,
  RoomMember_skip_value_,
  User_skip_id_,
  RoomMember
> {
  mapEntry(
    key: RoomMemberCompositeKey,
    values: Values<RoomMember_skip_value_>,
    context: Context,
  ): Iterable<[User_skip_id_, RoomMember]> {
    // > body
    const emits: [User_skip_id_, RoomMember][] = [];
    for (const value of values.toArray()) {
      const member: RoomMember = {
        roomId: key.roomId,
        userId: key.userId,
        joinedAt: value.joinedAt,
      };
      emits.push([key.userId, member]);
    }
    return emits;
    // < body
  }
}
