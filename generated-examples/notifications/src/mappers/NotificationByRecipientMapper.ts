import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Notification_skip_id_,
  Notification_skip_value_,
  User_skip_id_,
  Notification,
  User,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each notification entry, emit one output pair whose key is sourced from the entry's value's recipientUserId field, paired with a new value listing every required field of Notification explicitly: id sourced from the entry's key; recipientUserId sourced from the entry's value's recipientUserId field; type sourced from the entry's value's type field; targetId sourced from the entry's value's targetId field; eventCount sourced from the entry's value's eventCount field; firstEventAt sourced from the entry's value's firstEventAt field; lastEventAt sourced from the entry's value's lastEventAt field; createdAt sourced from the entry's value's createdAt field; updatedAt sourced from the entry's value's updatedAt field; recentActorUserIds sourced from the entry's value's recentActorUserIds field. The optional readAt field is present when the entry's value's readAt field is present, sourced from the entry's value's readAt field; absent otherwise.
export class NotificationByRecipientMapper implements Mapper<
  Notification_skip_id_,
  Notification_skip_value_,
  User_skip_id_,
  Notification
> {
  mapEntry(
    key: Notification_skip_id_,
    values: Values<Notification_skip_value_>,
    context: Context,
  ): Iterable<[User_skip_id_, Notification]> {
    // > body
    const emits: [User_skip_id_, Notification][] = [];
    for (const value of values.toArray()) {
      const notification: Notification = {
        id: key,
        recipientUserId: value.recipientUserId,
        type: value.type,
        targetId: value.targetId,
        eventCount: value.eventCount,
        firstEventAt: value.firstEventAt,
        lastEventAt: value.lastEventAt,
        createdAt: value.createdAt,
        updatedAt: value.updatedAt,
        recentActorUserIds: value.recentActorUserIds,
        ...(value.readAt !== undefined && { readAt: value.readAt }),
      };
      emits.push([value.recipientUserId, notification]);
    }
    return emits;
    // < body
  }
}
