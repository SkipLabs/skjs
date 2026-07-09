import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetComponentResource } from "./resources/GetComponentResource.js";
import { ListComponentsResource } from "./resources/ListComponentsResource.js";
import { SystemHealthCountsResource } from "./resources/SystemHealthCountsResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  Component_skip_id_,
  Component_skip_value_,
  User_skip_id_,
  User_skip_value_,
  ListComponentsParams,
  Component,
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
  readonly components: InputDefinition<
    Component_skip_id_,
    Component_skip_value_
  >;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getComponentResource: ResourceClass<GraphCollections, Json>;
  readonly listComponentsResource: ResourceClass<
    GraphCollections,
    ListComponentsParams
  >;
  readonly systemHealthCountsResource: ResourceClass<GraphCollections, Json>;
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
      components: new InputDefinition<
        Component_skip_id_,
        Component_skip_value_
      >([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      getComponentResource: GetComponentResource,
      listComponentsResource: ListComponentsResource,
      systemHealthCountsResource: SystemHealthCountsResource,
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
