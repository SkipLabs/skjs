import { UnreadNotificationByRecipientMapper } from "./mappers/UnreadNotificationByRecipientMapper.js";
import { SumReducer } from "./reducers/SumReducer.js";
import type {
  Notification_skip_id_,
  Notification,
  Notification_skip_value_,
  User_skip_id_,
  User,
  User_skip_value_,
  UnreadMarker,
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
  readonly unreadByRecipient: EagerCollection<User_skip_id_, UnreadMarker>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const output_notifications = inputs.notifications;
  const unreadMarkersByRecipient = inputs.notifications.map(
    UnreadNotificationByRecipientMapper,
  );
  const unreadCountByRecipient = unreadMarkersByRecipient.reduce(SumReducer);
  const output_unreadByRecipient = unreadCountByRecipient;
  const output_users = inputs.users;
  return {
    notifications: output_notifications,
    unreadByRecipient: output_unreadByRecipient,
    users: output_users,
  };
}
