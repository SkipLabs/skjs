import type {
  NotificationEventCompositeKey,
  NotificationEventStored,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface ListNotificationEventsStoredResourceInputs extends SharedCollections {
  readonly notificationEvents: EagerCollection<
    NotificationEventCompositeKey,
    NotificationEventStored
  >;
}

export class ListNotificationEventsStoredResource implements Resource<ListNotificationEventsStoredResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: ListNotificationEventsStoredResourceInputs,
    _context: Context,
  ): EagerCollection<NotificationEventCompositeKey, NotificationEventStored> {
    return inputs.notificationEvents;
  }
}
