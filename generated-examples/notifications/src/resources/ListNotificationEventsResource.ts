import type {
  Notification_skip_id_,
  NotificationEvent,
  Notification,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface ListNotificationEventsResourceInputs extends SharedCollections {
  readonly eventsByNotificationForList: EagerCollection<
    Notification_skip_id_,
    NotificationEvent
  >;
}

export class ListNotificationEventsResource implements Resource<ListNotificationEventsResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: ListNotificationEventsResourceInputs,
    _context: Context,
  ): EagerCollection<Notification_skip_id_, NotificationEvent> {
    return inputs.eventsByNotificationForList;
  }
}
