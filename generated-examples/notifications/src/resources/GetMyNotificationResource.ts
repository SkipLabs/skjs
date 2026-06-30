import { GetMyNotificationFullMapper } from "../mappers/GetMyNotificationFullMapper.js";
import type {
  Notification_skip_id_,
  NotificationEventChild,
  NotificationStored,
  NotificationFull,
  GetMyNotificationParams,
  Notification,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetMyNotificationResourceInputs extends SharedCollections {
  readonly notificationEventsByParent: EagerCollection<
    Notification_skip_id_,
    NotificationEventChild
  >;
  readonly notifications: EagerCollection<
    Notification_skip_id_,
    NotificationStored
  >;
}

export class GetMyNotificationResource implements Resource<GetMyNotificationResourceInputs> {
  private readonly notificationId: string;
  private readonly userId: string;

  constructor(params: GetMyNotificationParams) {
    this.notificationId = params.notificationId;
    this.userId = params.userId;
  }

  instantiate(
    inputs: GetMyNotificationResourceInputs,
    _context: Context,
  ): EagerCollection<Notification_skip_id_, NotificationFull> {
    return inputs.notifications.map(
      GetMyNotificationFullMapper,
      this.userId,
      this.notificationId,
      inputs.notificationEventsByParent,
    );
  }
}
