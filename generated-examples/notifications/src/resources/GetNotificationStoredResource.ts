import type {
  Notification_skip_id_,
  NotificationStored,
  Notification,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetNotificationStoredResourceInputs extends SharedCollections {
  readonly notifications: EagerCollection<
    Notification_skip_id_,
    NotificationStored
  >;
}

export class GetNotificationStoredResource implements Resource<GetNotificationStoredResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetNotificationStoredResourceInputs,
    _context: Context,
  ): EagerCollection<Notification_skip_id_, NotificationStored> {
    return inputs.notifications;
  }
}
