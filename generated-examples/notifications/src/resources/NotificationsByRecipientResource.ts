import { NotificationByRecipientMapper } from "../mappers/NotificationByRecipientMapper.js";
import type {
  Notification_skip_id_,
  NotificationStored,
  RecipientUserId,
  NotificationByRecipientValue,
  Notification,
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
    NotificationStored
  >;
}

export class NotificationsByRecipientResource implements Resource<NotificationsByRecipientResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: NotificationsByRecipientResourceInputs,
    _context: Context,
  ): EagerCollection<RecipientUserId, NotificationByRecipientValue> {
    const notificationsByRecipient = inputs.notifications.map(
      NotificationByRecipientMapper,
    );
    return notificationsByRecipient;
  }
}
