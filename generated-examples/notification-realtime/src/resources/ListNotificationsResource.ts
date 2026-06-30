import { FilterNotificationsForListMapper } from "../mappers/FilterNotificationsForListMapper.js";
import type {
  Notification_skip_id_,
  Notification_skip_value_,
  NotificationByRecipientCreatedKey,
  NotificationStatus,
  ListNotificationsParams,
  Notification,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListNotificationsResourceInputs extends SharedCollections {
  readonly notifications: EagerCollection<
    Notification_skip_id_,
    Notification_skip_value_
  >;
}

export class ListNotificationsResource implements Resource<ListNotificationsResourceInputs> {
  private readonly since: string | null;
  private readonly status: NotificationStatus | null;
  private readonly userId: string;

  constructor(params: ListNotificationsParams) {
    this.since = params.since ?? null;
    this.status = params.status ?? null;
    this.userId = params.userId;
  }

  instantiate(
    inputs: ListNotificationsResourceInputs,
    _context: Context,
  ): EagerCollection<
    NotificationByRecipientCreatedKey,
    Notification_skip_value_
  > {
    return inputs.notifications.map(
      FilterNotificationsForListMapper,
      this.userId,
      this.status,
      this.since,
    );
  }
}
