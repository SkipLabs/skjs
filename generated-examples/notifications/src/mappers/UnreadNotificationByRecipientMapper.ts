import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Notification_skip_id_,
  NotificationStored,
  User_skip_id_,
  UnreadTally,
  Notification,
  User,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each notification entry, when the entry's value's readAt field is absent, emit one output pair whose key is sourced from the entry's value's recipientUserId field and whose value is the literal one. Otherwise emit nothing. The original Notification.id (from the entry's key) is dropped: this collection feeds UnreadCountByUserMapper which sums the tally values per user and never needs to identify the source notification.
export class UnreadNotificationByRecipientMapper implements Mapper<
  Notification_skip_id_,
  NotificationStored,
  User_skip_id_,
  UnreadTally
> {
  mapEntry(
    key: Notification_skip_id_,
    values: Values<NotificationStored>,
    context: Context,
  ): Iterable<[User_skip_id_, UnreadTally]> {
    // > body
    const emits: [User_skip_id_, UnreadTally][] = [];
    for (const value of values.toArray()) {
      if (value.readAt === undefined) {
        emits.push([value.recipientUserId, 1]);
      }
    }
    return emits;
    // < body
  }
}
