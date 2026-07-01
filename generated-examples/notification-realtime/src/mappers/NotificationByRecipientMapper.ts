import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Notification_skip_id_,
  Notification_skip_value_,
  User_skip_id_,
  Notification,
  User,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each notification entry, emit one output pair whose key is sourced from the entry's value's recipientUserId field, paired with a new value listing every required field of Notification explicitly — id sourced from the entry's key (= the original Notification.id, preserved on the value side so downstream consumers consulting this collection by recipient can still identify each notification row); recipientUserId sourced from the entry's value's recipientUserId field; senderUserId sourced from the entry's value's senderUserId field; type sourced from the entry's value's type field; title sourced from the entry's value's title field; status sourced from the entry's value's status field; createdAt sourced from the entry's value's createdAt field — and every optional field of Notification explicitly: body present when the entry's value carries a body field, sourced from the entry's value's body field, absent otherwise; linkUrl present when the entry's value carries a linkUrl field, sourced from the entry's value's linkUrl field, absent otherwise; readAt present when the entry's value carries a readAt field, sourced from the entry's value's readAt field, absent otherwise.
export class NotificationByRecipientMapper implements Mapper<
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
    const emits: [string, Notification][] = [];
    for (const value of values.toArray()) {
      const notification: Notification = {
        id: key,
        recipientUserId: value.recipientUserId,
        senderUserId: value.senderUserId,
        type: value.type,
        title: value.title,
        status: value.status,
        createdAt: value.createdAt,
        ...(value.body !== undefined && { body: value.body }),
        ...(value.linkUrl !== undefined && { linkUrl: value.linkUrl }),
        ...(value.readAt !== undefined && { readAt: value.readAt }),
      };
      emits.push([value.recipientUserId, notification]);
    }
    return emits;
    // < body
  }
}
