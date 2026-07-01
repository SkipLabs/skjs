import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Notification_skip_id_,
  NotificationStored,
  RecipientUserId,
  UnreadCountValue,
  Notification,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each notification entry, when the entry's value readAt field is absent, emit one output pair whose key is sourced from the entry's recipientUserId field and whose value is the literal 1. Otherwise emit nothing. The original Notification id is dropped because the consumer aggregates counts per recipient and never reconstructs individual notification identities from this view.
export class NotificationUnreadCountByRecipientMapper implements Mapper<
  Notification_skip_id_,
  NotificationStored,
  RecipientUserId,
  UnreadCountValue
> {
  mapEntry(
    key: Notification_skip_id_,
    values: Values<NotificationStored>,
    context: Context,
  ): Iterable<[RecipientUserId, UnreadCountValue]> {
    // > body
    const emits: [RecipientUserId, UnreadCountValue][] = [];
    for (const value of values.toArray()) {
      if (value.readAt === undefined) {
        emits.push([value.recipientUserId, 1]);
      }
    }
    return emits;
    // < body
  }
}
