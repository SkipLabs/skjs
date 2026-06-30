import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Notification_skip_id_,
  Notification_skip_value_,
  NotificationByRecipientCreatedKey,
  Notification,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each notification entry, emit nothing when the entry's recipientUserId field does not equal the userId param. When the status param is present and the entry's status field does not equal the status param, emit nothing. When the since param is present and the entry's createdAt field (parsed to epoch milliseconds) is less than or equal to the since param (parsed to epoch milliseconds), emit nothing. Otherwise emit one output pair whose key is a composite record with recipientUserId sourced from the entry's recipientUserId field, negCreatedAt sourced from the negation of the entry's createdAt field parsed to epoch milliseconds (negated so ascending key ordering yields descending creation-time ordering), and id sourced from the entry's key — paired with the entry's value unchanged. The original Notification.id is encoded into the new key's id component; every required field of Notification_skip_value_ remains in the entry's value unchanged.
export class FilterNotificationsForListMapper implements Mapper<
  Notification_skip_id_,
  Notification_skip_value_,
  NotificationByRecipientCreatedKey,
  Notification_skip_value_
> {
  constructor(
    private userId: string,
    private status: string | null,
    private since: string | null,
  ) {}

  mapEntry(
    key: Notification_skip_id_,
    values: Values<Notification_skip_value_>,
    context: Context,
  ): Iterable<[NotificationByRecipientCreatedKey, Notification_skip_value_]> {
    // > body
    const emits: [
      NotificationByRecipientCreatedKey,
      Notification_skip_value_,
    ][] = [];
    for (const value of values.toArray()) {
      if (value.recipientUserId !== this.userId) continue;
      if (this.status !== null && value.status !== this.status) continue;
      const createdAtMs = Date.parse(value.createdAt);
      if (this.since !== null) {
        const sinceMs = Date.parse(this.since);
        if (createdAtMs <= sinceMs) continue;
      }
      const outKey: NotificationByRecipientCreatedKey = {
        id: key,
        negCreatedAt: -createdAtMs,
        recipientUserId: value.recipientUserId,
      };
      emits.push([outKey, value]);
    }
    return emits;
    // < body
  }
}
