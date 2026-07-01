import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Notification_skip_id_,
  NotificationEventChild,
  Notification,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each entry under the notificationId-keyed input: when the entry's key does not equal the notificationId param, emit nothing. Otherwise iterate the values associated with the key and for each value, emit one output pair whose key is the entry's key and whose value lists every required field of NotificationEventChild explicitly: id sourced from the value's id field; notificationId sourced from the value's notificationId field; actorUserId sourced from the value's actorUserId field; occurredAt sourced from the value's occurredAt field. The optional snippet field is present when the value has a snippet field, sourced from the value's snippet field; absent otherwise. (The input collection accumulates all NotificationEvent children for the same notification under one key — singleton-only access would raise on any notification with two or more events.)
export class FilterEventsByParentMapper implements Mapper<
  Notification_skip_id_,
  NotificationEventChild,
  Notification_skip_id_,
  NotificationEventChild
> {
  constructor(private notificationId: string) {}

  mapEntry(
    key: Notification_skip_id_,
    values: Values<NotificationEventChild>,
    context: Context,
  ): Iterable<[Notification_skip_id_, NotificationEventChild]> {
    // > body
    if (key !== this.notificationId) return [];
    const emits: [Notification_skip_id_, NotificationEventChild][] = [];
    for (const value of values.toArray()) {
      const child: NotificationEventChild = {
        id: value.id,
        notificationId: value.notificationId,
        actorUserId: value.actorUserId,
        occurredAt: value.occurredAt,
        ...(value.snippet !== undefined && { snippet: value.snippet }),
      };
      emits.push([key, child]);
    }
    return emits;
    // < body
  }
}
