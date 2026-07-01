import { NotificationByRecipientMapper } from "../mappers/NotificationByRecipientMapper.js";
import type {
  Notification_skip_id_,
  Notification_skip_value_,
  User_skip_id_,
  Notification,
  User,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface NotificationsByRecipientResourceInputs extends SharedCollections {
  readonly notifications: EagerCollection<
    Notification_skip_id_,
    Notification_skip_value_
  >;
}

export class NotificationsByRecipientResource implements Resource<NotificationsByRecipientResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: NotificationsByRecipientResourceInputs,
    _context: Context,
  ): EagerCollection<User_skip_id_, Notification> {
    return inputs.notifications.map(NotificationByRecipientMapper);
  }
}
