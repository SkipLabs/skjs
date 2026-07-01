import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  NotificationEventCompositeKey,
  NotificationEventStored,
  NotificationEvent,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each event entry, emit one output pair whose key is the entry's key unchanged and whose value lists every required field of NotificationEvent explicitly: notificationId sourced from the entry's key's notificationId field; eventId sourced from the entry's key's eventId field; actorUserId sourced from the entry's value's actorUserId field; createdAt sourced from the entry's value's createdAt field.
export class NotificationEventForListMapper implements Mapper<
  NotificationEventCompositeKey,
  NotificationEventStored,
  NotificationEventCompositeKey,
  NotificationEvent
> {
  mapEntry(
    key: NotificationEventCompositeKey,
    values: Values<NotificationEventStored>,
    context: Context,
  ): Iterable<[NotificationEventCompositeKey, NotificationEvent]> {
    // > body
    const emits: [NotificationEventCompositeKey, NotificationEvent][] = [];
    for (const value of values.toArray()) {
      const event: NotificationEvent = {
        notificationId: key.notificationId,
        eventId: key.eventId,
        actorUserId: value.actorUserId,
        createdAt: value.createdAt,
      };
      emits.push([key, event]);
    }
    return emits;
    // < body
  }
}
