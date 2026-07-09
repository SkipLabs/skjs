import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  NotificationEventCompositeKey,
  NotificationEvent,
  Notification_skip_id_,
  Notification,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each event entry, emit one output pair whose key is sourced from the entry's value's notificationId field, paired with the entry's value unchanged. The eventId component of the input key is preserved in the value's eventId field, so downstream consumers can reconstruct the full event.
export class NotificationEventByNotificationForListMapper implements Mapper<
  NotificationEventCompositeKey,
  NotificationEvent,
  Notification_skip_id_,
  NotificationEvent
> {
  mapEntry(
    key: NotificationEventCompositeKey,
    values: Values<NotificationEvent>,
    context: Context,
  ): Iterable<[Notification_skip_id_, NotificationEvent]> {
    // > body
    const emits: [Notification_skip_id_, NotificationEvent][] = [];
    for (const value of values.toArray()) {
      emits.push([value.notificationId, value]);
    }
    return emits;
    // < body
  }
}
