import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetActivityByIdResource } from "./resources/GetActivityByIdResource.js";
import { ListActivitiesResource } from "./resources/ListActivitiesResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  Activity_skip_id_,
  Activity_skip_value_,
  User_skip_id_,
  User_skip_value_,
  ListActivitiesParams,
  Activity,
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
  readonly activities: InputDefinition<Activity_skip_id_, Activity_skip_value_>;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getActivityByIdResource: ResourceClass<GraphCollections, Json>;
  readonly listActivitiesResource: ResourceClass<
    GraphCollections,
    ListActivitiesParams
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
      activities: new InputDefinition<Activity_skip_id_, Activity_skip_value_>(
        [],
      ),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      getActivityByIdResource: GetActivityByIdResource,
      listActivitiesResource: ListActivitiesResource,
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
