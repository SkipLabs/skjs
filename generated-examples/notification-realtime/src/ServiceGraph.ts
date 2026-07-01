import { NotificationsByUserWithIdMapper } from "./mappers/NotificationsByUserWithIdMapper.js";
import { UnreadCountByUserMapper } from "./mappers/UnreadCountByUserMapper.js";
import { UnreadNotificationByUserMapper } from "./mappers/UnreadNotificationByUserMapper.js";
import type {
  Notification_skip_id_,
  Notification,
  Notification_skip_value_,
  User_skip_id_,
  User,
  User_skip_value_,
  UnreadCount,
} from "./types.js";
import type {
  EagerCollection,
  Context,
  NamedEagerCollections,
  SharedCollections,
} from "@skipruntime/core";

export interface InputCollections extends NamedEagerCollections {
  readonly notifications: EagerCollection<
    Notification_skip_id_,
    Notification_skip_value_
  >;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export interface GraphCollections extends SharedCollections {
  readonly notifications: EagerCollection<
    Notification_skip_id_,
    Notification_skip_value_
  >;
  readonly notificationsByUser: EagerCollection<User_skip_id_, Notification>;
  readonly unreadCountByUser: EagerCollection<User_skip_id_, UnreadCount>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const notificationsByUser = inputs.notifications.map(
    NotificationsByUserWithIdMapper,
  );
  const output_notifications = inputs.notifications;
  const output_notificationsByUser = notificationsByUser;
  const unreadOnesByUser = notificationsByUser.map(
    UnreadNotificationByUserMapper,
  );
  const unreadCountByUser = inputs.users.map(
    UnreadCountByUserMapper,
    unreadOnesByUser,
  );
  const output_unreadCountByUser = unreadCountByUser;
  const output_users = inputs.users;
  return {
    notifications: output_notifications,
    notificationsByUser: output_notificationsByUser,
    unreadCountByUser: output_unreadCountByUser,
    users: output_users,
  };
}
