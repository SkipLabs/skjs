import { AssembleNotificationWithActorsMapper } from "./mappers/AssembleNotificationWithActorsMapper.js";
import { NotificationByRecipientMapper } from "./mappers/NotificationByRecipientMapper.js";
import { NotificationEventByNotificationForListMapper } from "./mappers/NotificationEventByNotificationForListMapper.js";
import { NotificationEventByNotificationMapper } from "./mappers/NotificationEventByNotificationMapper.js";
import { NotificationEventForListMapper } from "./mappers/NotificationEventForListMapper.js";
import { UnreadCountByUserMapper } from "./mappers/UnreadCountByUserMapper.js";
import { UnreadNotificationByRecipientMapper } from "./mappers/UnreadNotificationByRecipientMapper.js";
import type {
  NotificationEventCompositeKey,
  NotificationEventStored,
  Notification_skip_id_,
  Notification,
  NotificationStored,
  User_skip_id_,
  User,
  User_skip_value_,
  NotificationEvent,
  Notification_skip_value_,
  UnreadCount,
} from "./types.js";
import type {
  EagerCollection,
  Context,
  NamedEagerCollections,
  SharedCollections,
} from "@skipruntime/core";

export interface InputCollections extends NamedEagerCollections {
  readonly notificationEvents: EagerCollection<
    NotificationEventCompositeKey,
    NotificationEventStored
  >;
  readonly notifications: EagerCollection<
    Notification_skip_id_,
    NotificationStored
  >;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export interface GraphCollections extends SharedCollections {
  readonly eventsByNotificationForList: EagerCollection<
    Notification_skip_id_,
    NotificationEvent
  >;
  readonly notificationEvents: EagerCollection<
    NotificationEventCompositeKey,
    NotificationEventStored
  >;
  readonly notifications: EagerCollection<
    Notification_skip_id_,
    NotificationStored
  >;
  readonly notificationsByRecipient: EagerCollection<
    User_skip_id_,
    Notification
  >;
  readonly notificationsWithActors: EagerCollection<
    Notification_skip_id_,
    Notification_skip_value_
  >;
  readonly unreadCountByUser: EagerCollection<User_skip_id_, UnreadCount>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const eventsByNotification = inputs.notificationEvents.map(
    NotificationEventByNotificationMapper,
  );
  const notificationEventsForList = inputs.notificationEvents.map(
    NotificationEventForListMapper,
  );
  const eventsByNotificationForList = notificationEventsForList.map(
    NotificationEventByNotificationForListMapper,
  );
  const notificationsWithActors = inputs.notifications.map(
    AssembleNotificationWithActorsMapper,
    eventsByNotification,
  );
  const notificationsByRecipient = notificationsWithActors.map(
    NotificationByRecipientMapper,
  );
  const output_eventsByNotificationForList = eventsByNotificationForList;
  const output_notificationEvents = inputs.notificationEvents;
  const output_notifications = inputs.notifications;
  const output_notificationsByRecipient = notificationsByRecipient;
  const output_notificationsWithActors = notificationsWithActors;
  const unreadOnesByUser = inputs.notifications.map(
    UnreadNotificationByRecipientMapper,
  );
  const unreadCountByUser = inputs.users.map(
    UnreadCountByUserMapper,
    unreadOnesByUser,
  );
  const output_unreadCountByUser = unreadCountByUser;
  const output_users = inputs.users;
  return {
    eventsByNotificationForList: output_eventsByNotificationForList,
    notificationEvents: output_notificationEvents,
    notifications: output_notifications,
    notificationsByRecipient: output_notificationsByRecipient,
    notificationsWithActors: output_notificationsWithActors,
    unreadCountByUser: output_unreadCountByUser,
    users: output_users,
  };
}
