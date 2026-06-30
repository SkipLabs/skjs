import type {
  NotificationEvent_skip_id_,
  NotificationEvent_skip_value_,
  NotificationEvent,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListNotificationEventsRawResourceInputs extends SharedCollections {
  readonly notificationEvents: EagerCollection<
    NotificationEvent_skip_id_,
    NotificationEvent_skip_value_
  >;
}

export class ListNotificationEventsRawResource implements Resource<ListNotificationEventsRawResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: ListNotificationEventsRawResourceInputs,
    _context: Context,
  ): EagerCollection<
    NotificationEvent_skip_id_,
    NotificationEvent_skip_value_
  > {
    return inputs.notificationEvents;
  }
}
