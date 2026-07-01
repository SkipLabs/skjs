import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetNotificationStoredResource } from "./resources/GetNotificationStoredResource.js";
import { GetUnreadCountResource } from "./resources/GetUnreadCountResource.js";
import { ListAllNotificationsByUserResource } from "./resources/ListAllNotificationsByUserResource.js";
import { ListNotificationsByUserResource } from "./resources/ListNotificationsByUserResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  Notification_skip_id_,
  Notification_skip_value_,
  User_skip_id_,
  User_skip_value_,
  ListNotificationsParams,
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
  readonly notifications: InputDefinition<
    Notification_skip_id_,
    Notification_skip_value_
  >;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getNotificationStoredResource: ResourceClass<GraphCollections, Json>;
  readonly getUnreadCountResource: ResourceClass<GraphCollections, Json>;
  readonly listAllNotificationsByUserResource: ResourceClass<
    GraphCollections,
    Json
  >;
  readonly listNotificationsByUserResource: ResourceClass<
    GraphCollections,
    ListNotificationsParams
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
  externalServices: { [name: string]: ExternalService } = {};

  constructor() {
    this.inputs = {
      notifications: new InputDefinition<
        Notification_skip_id_,
        Notification_skip_value_
      >([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      getNotificationStoredResource: GetNotificationStoredResource,
      getUnreadCountResource: GetUnreadCountResource,
      listAllNotificationsByUserResource: ListAllNotificationsByUserResource,
      listNotificationsByUserResource: ListNotificationsByUserResource,
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
