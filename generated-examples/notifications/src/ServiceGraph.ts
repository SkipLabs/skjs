import { NotificationEventByParentMapper } from "./mappers/NotificationEventByParentMapper.js";
import { NotificationUnreadCountByRecipientMapper } from "./mappers/NotificationUnreadCountByRecipientMapper.js";
import { SumUnreadReducer } from "./reducers/SumUnreadReducer.js";
import type {
  NotificationEvent_skip_id_,
  NotificationEvent,
  NotificationEvent_skip_value_,
  Notification_skip_id_,
  Notification,
  NotificationStored,
  NotificationEventChild,
  RecipientUserId,
  UnreadCountAccum,
} from "./types.js";
import type {
  EagerCollection,
  Context,
  NamedEagerCollections,
  SharedCollections,
} from "@skipruntime/core";

export interface InputCollections extends NamedEagerCollections {
  readonly notificationEvents: EagerCollection<
    NotificationEvent_skip_id_,
    NotificationEvent_skip_value_
  >;
  readonly notifications: EagerCollection<
    Notification_skip_id_,
    NotificationStored
  >;
}

export interface GraphCollections extends SharedCollections {
  readonly notificationEvents: EagerCollection<
    NotificationEvent_skip_id_,
    NotificationEvent_skip_value_
  >;
  readonly notificationEventsByParent: EagerCollection<
    Notification_skip_id_,
    NotificationEventChild
  >;
  readonly notifications: EagerCollection<
    Notification_skip_id_,
    NotificationStored
  >;
  readonly unreadCountByRecipient: EagerCollection<
    RecipientUserId,
    UnreadCountAccum
  >;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const notificationEventsByParent = inputs.notificationEvents.map(
    NotificationEventByParentMapper,
  );
  const output_notificationEvents = inputs.notificationEvents;
  const output_notificationEventsByParent = notificationEventsByParent;
  const output_notifications = inputs.notifications;
  const unreadCountPerNotification = inputs.notifications.map(
    NotificationUnreadCountByRecipientMapper,
  );
  const unreadCountByRecipient =
    unreadCountPerNotification.reduce(SumUnreadReducer);
  const output_unreadCountByRecipient = unreadCountByRecipient;
  return {
    notificationEvents: output_notificationEvents,
    notificationEventsByParent: output_notificationEventsByParent,
    notifications: output_notifications,
    unreadCountByRecipient: output_unreadCountByRecipient,
  };
}
