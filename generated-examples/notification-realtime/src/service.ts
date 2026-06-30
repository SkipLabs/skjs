import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetNotificationResource } from "./resources/GetNotificationResource.js";
import { GetNotificationStoredResource } from "./resources/GetNotificationStoredResource.js";
import { GetUserByIdResource } from "./resources/GetUserByIdResource.js";
import { ListNotificationsResource } from "./resources/ListNotificationsResource.js";
import { NotificationsByRecipientResource } from "./resources/NotificationsByRecipientResource.js";
import { UnreadCountResource } from "./resources/UnreadCountResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  Notification_skip_id_,
  Notification_skip_value_,
  User_skip_id_,
  User_skip_value_,
  GetNotificationParams,
  GetUserByIdParams,
  ListNotificationsParams,
  UnreadCountParams,
  Notification,
  User,
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
  readonly notifications: InputDefinition<
    Notification_skip_id_,
    Notification_skip_value_
  >;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getNotificationResource: ResourceClass<
    GraphCollections,
    GetNotificationParams
  >;
  readonly getNotificationStoredResource: ResourceClass<GraphCollections, Json>;
  readonly getUserByIdResource: ResourceClass<
    GraphCollections,
    GetUserByIdParams
  >;
  readonly listNotificationsResource: ResourceClass<
    GraphCollections,
    ListNotificationsParams
  >;
  readonly notificationsByRecipientResource: ResourceClass<
    GraphCollections,
    Json
  >;
  readonly unreadCountResource: ResourceClass<
    GraphCollections,
    UnreadCountParams
  >;
  readonly getMeResource: ResourceClass<GraphCollections, Json>;
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
      notifications: new InputDefinition<
        Notification_skip_id_,
        Notification_skip_value_
      >([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      getNotificationResource: GetNotificationResource,
      getNotificationStoredResource: GetNotificationStoredResource,
      getUserByIdResource: GetUserByIdResource,
      listNotificationsResource: ListNotificationsResource,
      notificationsByRecipientResource: NotificationsByRecipientResource,
      unreadCountResource: UnreadCountResource,
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
