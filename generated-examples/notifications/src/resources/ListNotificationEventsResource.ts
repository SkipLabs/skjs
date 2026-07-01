import { FilterEventsByParentMapper } from "../mappers/FilterEventsByParentMapper.js";
import type {
  Notification_skip_id_,
  NotificationEventChild,
  ListNotificationEventsParams,
  Notification,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListNotificationEventsResourceInputs extends SharedCollections {
  readonly notificationEventsByParent: EagerCollection<
    Notification_skip_id_,
    NotificationEventChild
  >;
}

export class ListNotificationEventsResource implements Resource<ListNotificationEventsResourceInputs> {
  private readonly notificationId: string;

  constructor(params: ListNotificationEventsParams) {
    this.notificationId = params.notificationId;
  }

  instantiate(
    inputs: ListNotificationEventsResourceInputs,
    _context: Context,
  ): EagerCollection<Notification_skip_id_, NotificationEventChild> {
    return inputs.notificationEventsByParent.map(
      FilterEventsByParentMapper,
      this.notificationId,
    );
  }
}
