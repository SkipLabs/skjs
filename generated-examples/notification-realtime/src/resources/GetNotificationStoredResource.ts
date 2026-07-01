import type {
  Notification_skip_id_,
  Notification_skip_value_,
  Notification,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetNotificationStoredResourceInputs extends SharedCollections {
  readonly notifications: EagerCollection<
    Notification_skip_id_,
    Notification_skip_value_
  >;
}

export class GetNotificationStoredResource implements Resource<GetNotificationStoredResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: GetNotificationStoredResourceInputs,
    _context: Context,
  ): EagerCollection<Notification_skip_id_, Notification_skip_value_> {
    return inputs.notifications;
  }
}
