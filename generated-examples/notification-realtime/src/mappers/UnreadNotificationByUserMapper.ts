import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { User_skip_id_, Notification, UnreadOne, User } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each key (a userId), iterate the values associated with the key; for each value, when the value's readAt field is absent, emit one output pair whose key is the input key and whose value is the literal one. Otherwise emit nothing for that value. The input collection accumulates all notifications for the same user under one key (upstream re-key from notification id to userId), so singleton-only access would raise on any user with two or more notifications. Used to count unread notifications per user by summing the emitted ones.
export class UnreadNotificationByUserMapper implements Mapper<
  User_skip_id_,
  Notification,
  User_skip_id_,
  UnreadOne
> {
  mapEntry(
    key: User_skip_id_,
    values: Values<Notification>,
    context: Context,
  ): Iterable<[User_skip_id_, UnreadOne]> {
    // > body
    const emits: [User_skip_id_, UnreadOne][] = [];
    for (const value of values.toArray()) {
      if (value.readAt === undefined) {
        emits.push([key, 1]);
      }
    }
    return emits;
    // < body
  }
}
