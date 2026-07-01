import { GetNotificationMapper } from "../mappers/GetNotificationMapper.js";
import type {
  Notification_skip_id_,
  Notification_skip_value_,
  Notification,
  GetNotificationParams,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetNotificationResourceInputs extends SharedCollections {
  readonly notifications: EagerCollection<
    Notification_skip_id_,
    Notification_skip_value_
  >;
}

export class GetNotificationResource implements Resource<GetNotificationResourceInputs> {
  private readonly notificationId: string;
  private readonly userId: string;

  constructor(params: GetNotificationParams) {
    this.notificationId = params.notificationId;
    this.userId = params.userId;
  }

  instantiate(
    inputs: GetNotificationResourceInputs,
    _context: Context,
  ): EagerCollection<0, Notification> {
    return inputs.notifications.map(
      GetNotificationMapper,
      this.userId,
      this.notificationId,
    );
  }
}
