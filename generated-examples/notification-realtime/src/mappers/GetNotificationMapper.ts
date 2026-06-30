import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Notification_skip_id_,
  Notification_skip_value_,
  Notification,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each notification entry, emit nothing when the entry's key does not equal the notificationId param. Emit nothing when the entry's recipientUserId field does not equal the userId param (ownership check — non-recipients receive a not-found response from the api layer). Otherwise emit one output pair whose key is the literal-zero key and whose value lists every required field of Notification explicitly — id sourced from the entry's key; recipientUserId sourced from the entry's value's recipientUserId field; senderUserId sourced from the entry's value's senderUserId field; type sourced from the entry's value's type field; title sourced from the entry's value's title field; status sourced from the entry's value's status field; createdAt sourced from the entry's value's createdAt field — and every optional field of Notification explicitly — body present when the entry's value carries a body field, sourced from the entry's value's body field, absent otherwise; linkUrl present when the entry's value carries a linkUrl field, sourced from the entry's value's linkUrl field, absent otherwise; readAt present when the entry's value carries a readAt field, sourced from the entry's value's readAt field, absent otherwise.
export class GetNotificationMapper implements Mapper<
  Notification_skip_id_,
  Notification_skip_value_,
  0,
  Notification
> {
  constructor(
    private userId: string,
    private notificationId: string,
  ) {}

  mapEntry(
    key: Notification_skip_id_,
    values: Values<Notification_skip_value_>,
    context: Context,
  ): Iterable<[0, Notification]> {
    // > body
    if (key !== this.notificationId) return [];
    const emits: [0, Notification][] = [];
    for (const value of values.toArray()) {
      if (value.recipientUserId !== this.userId) continue;
      const out: Notification = {
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
      emits.push([0, out]);
    }
    return emits;
    // < body
  }
}
