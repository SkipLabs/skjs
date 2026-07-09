import type { User_skip_id_, Notification, User } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface ListAllNotificationsByUserResourceInputs extends SharedCollections {
  readonly notificationsByUser: EagerCollection<User_skip_id_, Notification>;
}

export class ListAllNotificationsByUserResource implements Resource<ListAllNotificationsByUserResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: ListAllNotificationsByUserResourceInputs,
    _context: Context,
  ): EagerCollection<User_skip_id_, Notification> {
    return inputs.notificationsByUser;
  }
}
