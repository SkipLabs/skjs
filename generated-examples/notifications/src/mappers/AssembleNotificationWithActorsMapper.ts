import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Notification_skip_id_,
  NotificationStored,
  Notification_skip_value_,
  NotificationEventStoredWithEventId,
  Notification,
} from "../types.js";
import type {
  Context,
  Mapper,
  Values,
  EagerCollection,
} from "@skipruntime/core";

// For each notification entry, consult eventsByNotification for the values indexed by the entry's key to obtain all raw event values for this notification group. Sort those event values by their createdAt field in descending order (most recent first), ties broken by the event value's eventId field ascending (eventId is a UUID and provides a total order, so no two event values can remain tied after this secondary key). Walk the sorted list and build recentActorUserIds by taking each event's actorUserId field, skipping any actorUserId that already appeared earlier in the walk (deduplicate preserving first occurrence), stopping once 5 distinct actorUserIds have been collected. Emit one output pair whose key is the entry's key unchanged and whose value lists every field of Notification_skip_value_ explicitly (the Notification.id primary key is excluded from _skip_value_ and is reconstructed from the entry's key at consumption time): recipientUserId sourced from the entry's value's recipientUserId field; type sourced from the entry's value's type field; targetId sourced from the entry's value's targetId field; eventCount sourced from the entry's value's eventCount field; firstEventAt sourced from the entry's value's firstEventAt field; lastEventAt sourced from the entry's value's lastEventAt field; createdAt sourced from the entry's value's createdAt field; updatedAt sourced from the entry's value's updatedAt field; recentActorUserIds sourced from the walked list computed above. The optional readAt field is present when the entry's value's readAt field is present, sourced from the entry's value's readAt field; absent otherwise.
export class AssembleNotificationWithActorsMapper implements Mapper<
  Notification_skip_id_,
  NotificationStored,
  Notification_skip_id_,
  Notification_skip_value_
> {
  constructor(
    private eventsByNotification: EagerCollection<
      Notification_skip_id_,
      NotificationEventStoredWithEventId
    >,
  ) {}

  mapEntry(
    key: Notification_skip_id_,
    values: Values<NotificationStored>,
    context: Context,
  ): Iterable<[Notification_skip_id_, Notification_skip_value_]> {
    // > body
    const stored = values.toArray()[0];
    if (stored === undefined) return [];

    const events = this.eventsByNotification.getArray(key).slice();
    events.sort((a, b) => {
      if (a.createdAt > b.createdAt) return -1;
      if (a.createdAt < b.createdAt) return 1;
      if (a.eventId < b.eventId) return -1;
      if (a.eventId > b.eventId) return 1;
      return 0;
    });

    const recentActorUserIds: string[] = [];
    const seen = new Set<string>();
    for (const event of events) {
      if (seen.has(event.actorUserId)) continue;
      seen.add(event.actorUserId);
      recentActorUserIds.push(event.actorUserId);
      if (recentActorUserIds.length >= 5) break;
    }

    const out: Notification_skip_value_ = {
      recipientUserId: stored.recipientUserId,
      type: stored.type,
      targetId: stored.targetId,
      eventCount: stored.eventCount,
      firstEventAt: stored.firstEventAt,
      lastEventAt: stored.lastEventAt,
      createdAt: stored.createdAt,
      updatedAt: stored.updatedAt,
      recentActorUserIds,
      ...(stored.readAt !== undefined && { readAt: stored.readAt }),
    };

    return [[key, out]];
    // < body
  }
}
