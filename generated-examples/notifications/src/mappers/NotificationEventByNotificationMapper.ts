import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  NotificationEventCompositeKey,
  NotificationEventStored,
  Notification_skip_id_,
  NotificationEventStoredWithEventId,
  Notification,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each event entry, emit one output pair whose key is sourced from the entry's key's notificationId field, paired with a new value whose eventId field is sourced from the entry's key's eventId field, whose actorUserId field is sourced from the entry's value's actorUserId field, and whose createdAt field is sourced from the entry's value's createdAt field. The eventId is re-injected on the value side (rather than dropped) because downstream consumers of this re-keyed collection consult it by notificationId and require the eventId to tie-break sort orders — the composite-key eventId component would otherwise be unrecoverable once the key is projected to notificationId.
export class NotificationEventByNotificationMapper implements Mapper<
  NotificationEventCompositeKey,
  NotificationEventStored,
  Notification_skip_id_,
  NotificationEventStoredWithEventId
> {
  mapEntry(
    key: NotificationEventCompositeKey,
    values: Values<NotificationEventStored>,
    context: Context,
  ): Iterable<[Notification_skip_id_, NotificationEventStoredWithEventId]> {
    // > body
    const emits: [Notification_skip_id_, NotificationEventStoredWithEventId][] =
      [];
    for (const value of values.toArray()) {
      emits.push([
        key.notificationId,
        {
          eventId: key.eventId,
          actorUserId: value.actorUserId,
          createdAt: value.createdAt,
        },
      ]);
    }
    return emits;
    // < body
  }
}
