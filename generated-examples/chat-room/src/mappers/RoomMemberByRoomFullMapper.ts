import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  RoomMemberCompositeKey,
  RoomMember_skip_value_,
  Room_skip_id_,
  RoomMember,
  Room,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each room member entry, emit one output pair whose key is sourced from the entry's key roomId field (the Room primary key), paired with a full RoomMember record. The output value lists every required field of RoomMember explicitly: roomId sourced from the entry's key roomId field; userId sourced from the entry's key userId field; joinedAt sourced from the entry's value joinedAt field. This re-key drops the userId from the key and re-injects it into the value so downstream consumers (member listing, membership checks) can reconstruct full RoomMember entities. The original roomId is encoded into the new key.
export class RoomMemberByRoomFullMapper implements Mapper<
  RoomMemberCompositeKey,
  RoomMember_skip_value_,
  Room_skip_id_,
  RoomMember
> {
  mapEntry(
    key: RoomMemberCompositeKey,
    values: Values<RoomMember_skip_value_>,
    context: Context,
  ): Iterable<[Room_skip_id_, RoomMember]> {
    // > body
    const emits: [Room_skip_id_, RoomMember][] = [];
    for (const value of values.toArray()) {
      emits.push([
        key.roomId,
        {
          roomId: key.roomId,
          userId: key.userId,
          joinedAt: value.joinedAt,
        },
      ]);
    }
    return emits;
    // < body
  }
}
