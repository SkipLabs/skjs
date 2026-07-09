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
  Json,
} from "@skipruntime/core";

export interface GetNotificationResourceInputs extends SharedCollections {
  readonly notificationsWithActors: EagerCollection<
    Notification_skip_id_,
    Notification_skip_value_
  >;
}

export class GetNotificationResource implements Resource<GetNotificationResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetNotificationResourceInputs,
    _context: Context,
  ): EagerCollection<Notification_skip_id_, Notification_skip_value_> {
    return inputs.notificationsWithActors;
  }
}
