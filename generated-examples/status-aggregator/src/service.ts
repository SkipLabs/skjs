import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetComponentResource } from "./resources/GetComponentResource.js";
import { GetSystemHealthResource } from "./resources/GetSystemHealthResource.js";
import { ListComponentsResource } from "./resources/ListComponentsResource.js";
import { ListHeartbeatsResource } from "./resources/ListHeartbeatsResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  Component_skip_id_,
  ComponentStored,
  Heartbeat_skip_id_,
  Heartbeat_skip_value_,
  User_skip_id_,
  User_skip_value_,
  ListComponentsParams,
  Component,
  Heartbeat,
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
  readonly components: InputDefinition<Component_skip_id_, ComponentStored>;
  readonly heartbeats: InputDefinition<
    Heartbeat_skip_id_,
    Heartbeat_skip_value_
  >;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getComponentResource: ResourceClass<GraphCollections, Json>;
  readonly getSystemHealthResource: ResourceClass<GraphCollections, Json>;
  readonly listComponentsResource: ResourceClass<
    GraphCollections,
    ListComponentsParams
  >;
  readonly listHeartbeatsResource: ResourceClass<GraphCollections, Json>;
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
      components: new InputDefinition<Component_skip_id_, ComponentStored>([]),
      heartbeats: new InputDefinition<
        Heartbeat_skip_id_,
        Heartbeat_skip_value_
      >([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      getComponentResource: GetComponentResource,
      getSystemHealthResource: GetSystemHealthResource,
      listComponentsResource: ListComponentsResource,
      listHeartbeatsResource: ListHeartbeatsResource,
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
