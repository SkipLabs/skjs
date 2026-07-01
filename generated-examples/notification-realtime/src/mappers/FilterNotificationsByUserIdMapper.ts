import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { User_skip_id_, Notification, User } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each key, when the key does not equal the userId param, emit nothing; otherwise iterate the values associated with the key and for each value, emit one output pair whose key is the entry's key and whose value is that value. The input collection accumulates all notifications for the same user under one key (upstream re-key from notification id to userId), so singleton-only access would raise on any user with two or more notifications. Used to scope the per-user notifications view to the authenticated caller.
export class FilterNotificationsByUserIdMapper implements Mapper<
  User_skip_id_,
  Notification,
  User_skip_id_,
  Notification
> {
  constructor(private userId: string) {}

  mapEntry(
    key: User_skip_id_,
    values: Values<Notification>,
    context: Context,
  ): Iterable<[User_skip_id_, Notification]> {
    // > body
    if (key !== this.userId) return [];
    const emits: [User_skip_id_, Notification][] = [];
    for (const value of values.toArray()) {
      emits.push([key, value]);
    }
    return emits;
    // < body
  }
}
