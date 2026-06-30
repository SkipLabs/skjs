import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  RoomMembershipKey,
  RoomMembership_skip_value_,
  Room_skip_id_,
  RoomMembership,
  Room,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each membership entry, emit one output pair whose key is sourced from the entry's key's roomId field (a foreign key to Room, so the new key type is Room_skip_id_), paired with a new value listing every required field of RoomMembership explicitly — the roomId field sourced from the entry's key's roomId field, the userId field sourced from the entry's key's userId field (re-injected on the value side because the new key drops it), and the joinedAt field sourced from the entry's value's joinedAt field. This preserves both composite-PK components on the output even though the new key only carries roomId.
export class MembershipByRoomMapper implements Mapper<
  RoomMembershipKey,
  RoomMembership_skip_value_,
  Room_skip_id_,
  RoomMembership
> {
  mapEntry(
    key: RoomMembershipKey,
    values: Values<RoomMembership_skip_value_>,
    context: Context,
  ): Iterable<[Room_skip_id_, RoomMembership]> {
    // > body
    const emits: [Room_skip_id_, RoomMembership][] = [];
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
