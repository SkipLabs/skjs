import { AssembleNotificationFullMapper } from "../mappers/AssembleNotificationFullMapper.js";
import type {
  Notification_skip_id_,
  NotificationEventChild,
  NotificationStored,
  NotificationFull,
  ListMyNotificationsParams,
  Notification,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  DepSafe,
} from "@skipruntime/core";
import { deepFreeze } from "@skipruntime/core";

export interface ListMyNotificationsResourceInputs extends SharedCollections {
  readonly notificationEventsByParent: EagerCollection<
    Notification_skip_id_,
    NotificationEventChild
  >;
  readonly notifications: EagerCollection<
    Notification_skip_id_,
    NotificationStored
  >;
}

export class ListMyNotificationsResource implements Resource<ListMyNotificationsResourceInputs> {
  private readonly type: (("mention" | "follow" | "like") & DepSafe) | null;
  private readonly unreadOnly: boolean | null;
  private readonly userId: string;

  constructor(params: ListMyNotificationsParams) {
    this.type = deepFreeze(params.type ?? null);
    this.unreadOnly = params.unreadOnly ?? null;
    this.userId = params.userId;
  }

  instantiate(
    inputs: ListMyNotificationsResourceInputs,
    _context: Context,
  ): EagerCollection<Notification_skip_id_, NotificationFull> {
    return inputs.notifications.map(
      AssembleNotificationFullMapper,
      this.userId,
      inputs.notificationEventsByParent,
      this.unreadOnly,
      this.type,
    );
  }
}
