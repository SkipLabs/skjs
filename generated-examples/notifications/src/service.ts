import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetMyNotificationResource } from "./resources/GetMyNotificationResource.js";
import { GetMyUnreadCountResource } from "./resources/GetMyUnreadCountResource.js";
import { GetNotificationStoredResource } from "./resources/GetNotificationStoredResource.js";
import { ListMyNotificationsResource } from "./resources/ListMyNotificationsResource.js";
import { ListNotificationEventsRawResource } from "./resources/ListNotificationEventsRawResource.js";
import { ListNotificationEventsResource } from "./resources/ListNotificationEventsResource.js";
import { NotificationsByRecipientResource } from "./resources/NotificationsByRecipientResource.js";
import type {
  NotificationEvent_skip_id_,
  NotificationEvent_skip_value_,
  Notification_skip_id_,
  NotificationStored,
  GetMyNotificationParams,
  UnreadCountParams,
  ListMyNotificationsParams,
  ListNotificationEventsParams,
  NotificationEvent,
  Notification,
} from "./types.js";
import type {
  SkipService,
  ResourceClass,
  Context,
  NamedInputDefinitions,
  NamedResources,
  Json,
} from "@skipruntime/core";
import { InputDefinition } from "@skipruntime/core";

interface Inputs extends NamedInputDefinitions {
  readonly notificationEvents: InputDefinition<
    NotificationEvent_skip_id_,
    NotificationEvent_skip_value_
  >;
  readonly notifications: InputDefinition<
    Notification_skip_id_,
    NotificationStored
  >;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getMyNotificationResource: ResourceClass<
    GraphCollections,
    GetMyNotificationParams
  >;
  readonly getMyUnreadCountResource: ResourceClass<
    GraphCollections,
    UnreadCountParams
  >;
  readonly getNotificationStoredResource: ResourceClass<GraphCollections, Json>;
  readonly listMyNotificationsResource: ResourceClass<
    GraphCollections,
    ListMyNotificationsParams
  >;
  readonly listNotificationEventsRawResource: ResourceClass<
    GraphCollections,
    Json
  >;
  readonly listNotificationEventsResource: ResourceClass<
    GraphCollections,
    ListNotificationEventsParams
  >;
  readonly notificationsByRecipientResource: ResourceClass<
    GraphCollections,
    Json
  >;
}

class Service implements SkipService<
  Inputs,
  InputCollections,
  GraphCollections
> {
  readonly inputs: Inputs;
  readonly resources: Resources;

  constructor() {
    this.inputs = {
      notificationEvents: new InputDefinition<
        NotificationEvent_skip_id_,
        NotificationEvent_skip_value_
      >([]),
      notifications: new InputDefinition<
        Notification_skip_id_,
        NotificationStored
      >([]),
    };
    this.resources = {
      getMyNotificationResource: GetMyNotificationResource,
      getMyUnreadCountResource: GetMyUnreadCountResource,
      getNotificationStoredResource: GetNotificationStoredResource,
      listMyNotificationsResource: ListMyNotificationsResource,
      listNotificationEventsRawResource: ListNotificationEventsRawResource,
      listNotificationEventsResource: ListNotificationEventsResource,
      notificationsByRecipientResource: NotificationsByRecipientResource,
    };
  }

  createGraph(inputs: InputCollections, context: Context): GraphCollections {
    return createGraph(inputs, context);
  }
}

export function service(): SkipService<
  Inputs,
  InputCollections,
  GraphCollections
> {
  return new Service();
}
