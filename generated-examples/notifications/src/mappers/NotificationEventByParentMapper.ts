import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  NotificationEvent_skip_id_,
  NotificationEvent_skip_value_,
  Notification_skip_id_,
  NotificationEventChild,
  NotificationEvent,
  Notification,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each event entry, emit one output pair whose key is sourced from the entry's key notificationId field and whose value lists every required field of NotificationEventChild explicitly: id sourced from the entry's key id field; notificationId sourced from the entry's key notificationId field; actorUserId sourced from the entry's value actorUserId field; occurredAt sourced from the entry's value occurredAt field. The optional snippet field is present when the entry's value has a snippet field, sourced from the entry's value snippet field; absent otherwise. The original key notificationId is preserved both in the new output key and in the value's notificationId field; the original key id is preserved in the value's id field.
export class NotificationEventByParentMapper implements Mapper<
  NotificationEvent_skip_id_,
  NotificationEvent_skip_value_,
  Notification_skip_id_,
  NotificationEventChild
> {
  mapEntry(
    key: NotificationEvent_skip_id_,
    values: Values<NotificationEvent_skip_value_>,
    context: Context,
  ): Iterable<[Notification_skip_id_, NotificationEventChild]> {
    // > body
    const emits: [Notification_skip_id_, NotificationEventChild][] = [];
    for (const value of values.toArray()) {
      const child: NotificationEventChild = {
        id: key.id,
        notificationId: key.notificationId,
        actorUserId: value.actorUserId,
        occurredAt: value.occurredAt,
        ...(value.snippet !== undefined && { snippet: value.snippet }),
      };
      emits.push([key.notificationId, child]);
    }
    return emits;
    // < body
  }
}
