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

// For each notification entry, when the entry's value recipientUserId field does not equal the userId param, emit nothing. Otherwise, when the unreadOnly param is present and equals true AND the entry's value readAt field is present, emit nothing. Otherwise, when the type param is present AND the entry's value type field does not equal the type param, emit nothing. Otherwise consult the eventsByParent lazy collection at the entry's key to retrieve every NotificationEventChild value associated with that notification id; iterate the values associated with the key to compute three derived figures: eventCount is the count of those values; actorCount is the count of distinct actorUserId values among those values; recentActorUserIds is computed as follows — first sort all retrieved values into a totally-ordered list by occurredAt descending (lexicographic descending on the date-time string), ties broken by actorUserId ascending (lexicographic ascending), then ties broken by id ascending (lexicographic ascending); then walk that sorted list in order and collect actorUserId values, skipping any actorUserId already collected, stopping once 3 distinct actorUserId values have been collected (or the list is exhausted, whichever comes first); the result is the resulting list of distinct actorUserId values in collection order. Then emit one output pair whose key is the entry's key and whose value lists every required field of NotificationFull explicitly: id sourced from the entry's key; recipientUserId sourced from the entry's value recipientUserId field; type sourced from the entry's value type field; targetType sourced from the entry's value targetType field; targetId sourced from the entry's value targetId field; eventCount, actorCount, recentActorUserIds sourced from the computations above; createdAt sourced from the entry's value createdAt field; lastEventAt sourced from the entry's value lastEventAt field. The optional readAt field is present when the entry's value has a readAt field, sourced from the entry's value readAt field; absent otherwise.
export class AssembleNotificationFullMapper implements Mapper<
  Notification_skip_id_,
  NotificationStored,
  Notification_skip_id_,
  NotificationFull
> {
  constructor(
    private userId: string,
    private eventsByParent: LazyCollection<
      Notification_skip_id_,
      NotificationEventChild
    >,
    private unreadOnly: boolean | null,
    private type: string | null,
  ) {}

  mapEntry(
    key: Notification_skip_id_,
    values: Values<NotificationStored>,
    context: Context,
  ): Iterable<[Notification_skip_id_, NotificationFull]> {
    // > body
    const emits: [Notification_skip_id_, NotificationFull][] = [];
    for (const value of values.toArray()) {
      if (value.recipientUserId !== this.userId) continue;
      if (this.unreadOnly === true && value.readAt !== undefined) continue;
      if (
        this.type !== null &&
        this.type !== undefined &&
        value.type !== this.type
      )
        continue;

      const events = this.eventsByParent.getArray(key);
      const eventCount = events.length;

      const sorted = events.slice().sort((a, b) => {
        if (a.occurredAt > b.occurredAt) return -1;
        if (a.occurredAt < b.occurredAt) return 1;
        if (a.actorUserId < b.actorUserId) return -1;
        if (a.actorUserId > b.actorUserId) return 1;
        if (a.id < b.id) return -1;
        if (a.id > b.id) return 1;
        return 0;
      });

      const seen = new Set<string>();
      const recentActorUserIds: string[] = [];
      for (const ev of sorted) {
        if (seen.has(ev.actorUserId)) continue;
        seen.add(ev.actorUserId);
        if (recentActorUserIds.length < 3) {
          recentActorUserIds.push(ev.actorUserId);
        }
        if (recentActorUserIds.length >= 3) break;
      }

      const actorSet = new Set<string>();
      for (const ev of events) actorSet.add(ev.actorUserId);
      const actorCount = actorSet.size;

      const full: NotificationFull = {
        id: key,
        recipientUserId: value.recipientUserId,
        type: value.type,
        targetType: value.targetType,
        targetId: value.targetId,
        eventCount,
        actorCount,
        recentActorUserIds,
        createdAt: value.createdAt,
        lastEventAt: value.lastEventAt,
        ...(value.readAt !== undefined && { readAt: value.readAt }),
      };
      emits.push([key, full]);
    }
    return emits;
    // < body
  }
}
