import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Notification_skip_id_,
  Notification_skip_value_,
  User_skip_id_,
  Notification,
  User,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each notification entry, emit one output pair whose key is sourced from the entry's value userId field (a User primary key), paired with a value listing every required field of Notification explicitly — id sourced from the entry's key; userId, type, title, createdAt sourced from the entry's value; body, linkUrl, readAt sourced from the entry's value when present (each optional: present when the entry's value has that field, absent otherwise). The original notification id from from[0] is preserved in the value's id field so downstream consumers can reconstruct the full Notification entity.
export class NotificationsByUserWithIdMapper implements Mapper<
  Notification_skip_id_,
  Notification_skip_value_,
  User_skip_id_,
  Notification
> {
  mapEntry(
    key: Notification_skip_id_,
    values: Values<Notification_skip_value_>,
    context: Context,
  ): Iterable<[User_skip_id_, Notification]> {
    // > body
    const emits: [User_skip_id_, Notification][] = [];
    for (const value of values.toArray()) {
      const notification: Notification = {
        id: key,
        userId: value.userId,
        type: value.type,
        title: value.title,
        createdAt: value.createdAt,
        ...(value.body !== undefined && { body: value.body }),
        ...(value.linkUrl !== undefined && { linkUrl: value.linkUrl }),
        ...(value.readAt !== undefined && { readAt: value.readAt }),
      };
      emits.push([value.userId, notification]);
    }
    return emits;
    // < body
  }
}
