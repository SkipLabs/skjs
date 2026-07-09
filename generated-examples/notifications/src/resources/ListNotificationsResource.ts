import type { User_skip_id_, Notification, User } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface ListNotificationsResourceInputs extends SharedCollections {
  readonly notificationsByRecipient: EagerCollection<
    User_skip_id_,
    Notification
  >;
}

export class ListNotificationsResource implements Resource<ListNotificationsResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: ListNotificationsResourceInputs,
    _context: Context,
  ): EagerCollection<User_skip_id_, Notification> {
    return inputs.notificationsByRecipient;
  }
}
