import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Notification_skip_id_,
  NotificationStored,
  RecipientUserId,
  NotificationByRecipientValue,
  Notification,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each notification entry, emit one output pair whose key is sourced from the entry's value recipientUserId field and whose value lists every required field of NotificationByRecipientValue explicitly: id sourced from the entry's key; recipientUserId sourced from the entry's value recipientUserId field; type sourced from the entry's value type field; targetType sourced from the entry's value targetType field; targetId sourced from the entry's value targetId field; createdAt sourced from the entry's value createdAt field; lastEventAt sourced from the entry's value lastEventAt field. The optional readAt field is present when the entry's value has a readAt field, sourced from the entry's value readAt field; absent otherwise. The original Notification id is preserved on the value side as the id field so that consumers (mark-all-read enumerating the caller's notifications) can address each row by its full id when applying incremental updates.
export class NotificationByRecipientMapper implements Mapper<
  Notification_skip_id_,
  NotificationStored,
  RecipientUserId,
  NotificationByRecipientValue
> {
  mapEntry(
    key: Notification_skip_id_,
    values: Values<NotificationStored>,
    context: Context,
  ): Iterable<[RecipientUserId, NotificationByRecipientValue]> {
    // > body
    const emits: [RecipientUserId, NotificationByRecipientValue][] = [];
    for (const value of values.toArray()) {
      const out: NotificationByRecipientValue = {
        id: key,
        recipientUserId: value.recipientUserId,
        type: value.type,
        targetType: value.targetType,
        targetId: value.targetId,
        createdAt: value.createdAt,
        lastEventAt: value.lastEventAt,
        ...(value.readAt !== undefined && { readAt: value.readAt }),
      };
      emits.push([value.recipientUserId, out]);
    }
    return emits;
    // < body
  }
}
