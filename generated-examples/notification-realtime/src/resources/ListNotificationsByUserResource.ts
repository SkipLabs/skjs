import { FilterNotificationsByUserIdMapper } from "../mappers/FilterNotificationsByUserIdMapper.js";
import type {
  User_skip_id_,
  Notification,
  ListNotificationsParams,
  User,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListNotificationsByUserResourceInputs extends SharedCollections {
  readonly notificationsByUser: EagerCollection<User_skip_id_, Notification>;
}

export class ListNotificationsByUserResource implements Resource<ListNotificationsByUserResourceInputs> {
  private readonly userId: string;

  constructor(params: ListNotificationsParams) {
    this.userId = params.userId;
  }

  instantiate(
    inputs: ListNotificationsByUserResourceInputs,
    _context: Context,
  ): EagerCollection<User_skip_id_, Notification> {
    return inputs.notificationsByUser.map(
      FilterNotificationsByUserIdMapper,
      this.userId,
    );
  }
}
