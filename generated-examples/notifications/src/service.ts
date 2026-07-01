import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetNotificationResource } from "./resources/GetNotificationResource.js";
import { GetNotificationStoredResource } from "./resources/GetNotificationStoredResource.js";
import { GetUnreadCountResource } from "./resources/GetUnreadCountResource.js";
import { ListNotificationEventsResource } from "./resources/ListNotificationEventsResource.js";
import { ListNotificationEventsStoredResource } from "./resources/ListNotificationEventsStoredResource.js";
import { ListNotificationsResource } from "./resources/ListNotificationsResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  NotificationEventCompositeKey,
  NotificationEventStored,
  Notification_skip_id_,
  NotificationStored,
  User_skip_id_,
  User_skip_value_,
  Notification,
  User,
} from "./types.js";
import type {
  SkipService,
  ResourceClass,
  Context,
  ExternalService,
  NamedInputDefinitions,
  NamedResources,
  Json,
} from "@skipruntime/core";
import { InputDefinition } from "@skipruntime/core";

interface Inputs extends NamedInputDefinitions {
  readonly notificationEvents: InputDefinition<
    NotificationEventCompositeKey,
    NotificationEventStored
  >;
  readonly notifications: InputDefinition<
    Notification_skip_id_,
    NotificationStored
  >;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getNotificationResource: ResourceClass<GraphCollections, Json>;
  readonly getNotificationStoredResource: ResourceClass<GraphCollections, Json>;
  readonly getUnreadCountResource: ResourceClass<GraphCollections, Json>;
  readonly listNotificationEventsResource: ResourceClass<
    GraphCollections,
    Json
  >;
  readonly listNotificationEventsStoredResource: ResourceClass<
    GraphCollections,
    Json
  >;
  readonly listNotificationsResource: ResourceClass<GraphCollections, Json>;
  readonly getMeResource: ResourceClass<GraphCollections, Json>;
}

class Service implements SkipService<
  Inputs,
  InputCollections,
  GraphCollections
> {
  readonly inputs: Inputs;
  readonly resources: Resources;
  externalServices: { [name: string]: ExternalService } = {};

  constructor() {
    this.inputs = {
      notificationEvents: new InputDefinition<
        NotificationEventCompositeKey,
        NotificationEventStored
      >([]),
      notifications: new InputDefinition<
        Notification_skip_id_,
        NotificationStored
      >([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      getNotificationResource: GetNotificationResource,
      getNotificationStoredResource: GetNotificationStoredResource,
      getUnreadCountResource: GetUnreadCountResource,
      listNotificationEventsResource: ListNotificationEventsResource,
      listNotificationEventsStoredResource:
        ListNotificationEventsStoredResource,
      listNotificationsResource: ListNotificationsResource,
      getMeResource: getMeResource,
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
