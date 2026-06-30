import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Notification_skip_id_,
  NotificationStored,
  NotificationFull,
  NotificationEventChild,
  Notification,
} from "../types.js";
import type {
  Context,
  Mapper,
  Values,
  LazyCollection,
} from "@skipruntime/core";

// For each notification entry, when the entry's key does not equal the notificationId param, emit nothing. Otherwise, when the entry's value recipientUserId field does not equal the userId param, emit nothing. Otherwise consult the eventsByParent lazy collection at the entry's key to retrieve every NotificationEventChild value associated with that notification id; iterate the values associated with the key to compute three derived figures: eventCount is the count of those values; actorCount is the count of distinct actorUserId values among those values; recentActorUserIds is computed as follows — first sort all retrieved values into a totally-ordered list by occurredAt descending (lexicographic descending on the date-time string), ties broken by actorUserId ascending (lexicographic ascending), then ties broken by id ascending (lexicographic ascending); then walk that sorted list in order and collect actorUserId values, skipping any actorUserId already collected, stopping once 3 distinct actorUserId values have been collected (or the list is exhausted, whichever comes first); the result is the resulting list of distinct actorUserId values in collection order. Then emit one output pair whose key is the entry's key and whose value lists every required field of NotificationFull explicitly: id sourced from the entry's key; recipientUserId sourced from the entry's value recipientUserId field; type sourced from the entry's value type field; targetType sourced from the entry's value targetType field; targetId sourced from the entry's value targetId field; eventCount, actorCount, recentActorUserIds sourced from the computations above; createdAt sourced from the entry's value createdAt field; lastEventAt sourced from the entry's value lastEventAt field. The optional readAt field is present when the entry's value has a readAt field, sourced from the entry's value readAt field; absent otherwise.
export class GetMyNotificationFullMapper implements Mapper<
  Notification_skip_id_,
  NotificationStored,
  Notification_skip_id_,
  NotificationFull
> {
  constructor(
    private userId: string,
    private notificationId: string,
    private eventsByParent: LazyCollection<
      Notification_skip_id_,
      NotificationEventChild
    >,
  ) {}

  mapEntry(
    key: Notification_skip_id_,
    values: Values<NotificationStored>,
    context: Context,
  ): Iterable<[Notification_skip_id_, NotificationFull]> {
    // > body
    if (key !== this.notificationId) return [];
    const stored = values.toArray()[0];
    if (stored === undefined) return [];
    if (stored.recipientUserId !== this.userId) return [];

    const events = this.eventsByParent.getArray(key);
    const eventCount = events.length;

    const distinctActors = new Set<string>();
    for (const e of events) distinctActors.add(e.actorUserId);
    const actorCount = distinctActors.size;

    const sorted = events.slice().sort((a, b) => {
      if (a.occurredAt > b.occurredAt) return -1;
      if (a.occurredAt < b.occurredAt) return 1;
      if (a.actorUserId < b.actorUserId) return -1;
      if (a.actorUserId > b.actorUserId) return 1;
      if (a.id < b.id) return -1;
      if (a.id > b.id) return 1;
      return 0;
    });

    const recentActorUserIds: string[] = [];
    const seen = new Set<string>();
    for (const e of sorted) {
      if (seen.has(e.actorUserId)) continue;
      seen.add(e.actorUserId);
      recentActorUserIds.push(e.actorUserId);
      if (recentActorUserIds.length >= 3) break;
    }

    const full: NotificationFull = {
      id: key,
      recipientUserId: stored.recipientUserId,
      type: stored.type,
      targetType: stored.targetType,
      targetId: stored.targetId,
      eventCount,
      actorCount,
      recentActorUserIds,
      createdAt: stored.createdAt,
      lastEventAt: stored.lastEventAt,
      ...(stored.readAt !== undefined && { readAt: stored.readAt }),
    };

    return [[key, full]];
    // < body
  }
}
