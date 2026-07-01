import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Notification_skip_id_,
  Notification_skip_value_,
  User_skip_id_,
  UnreadMarker,
  Notification,
  User,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each notification entry, emit nothing when the entry's status field does not equal the literal "UNREAD". Otherwise emit one output pair whose key is sourced from the entry's recipientUserId field and whose value is the literal 1. The original Notification.id is dropped: this collection feeds the unread-count reducer (SumReducer over UnreadMarker) which only aggregates per recipient and never needs to identify individual notifications.
export class UnreadNotificationByRecipientMapper implements Mapper<
  Notification_skip_id_,
  Notification_skip_value_,
  User_skip_id_,
  UnreadMarker
> {
  mapEntry(
    key: Notification_skip_id_,
    values: Values<Notification_skip_value_>,
    context: Context,
  ): Iterable<[User_skip_id_, UnreadMarker]> {
    // > body
    const emits: [User_skip_id_, UnreadMarker][] = [];
    for (const value of values.toArray()) {
      if (value.status === "UNREAD") {
        emits.push([value.recipientUserId, 1]);
      }
    }
    return emits;
    // < body
  }
}
