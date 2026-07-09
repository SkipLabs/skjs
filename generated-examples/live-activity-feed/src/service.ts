import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { FollowsByFollowerResource } from "./resources/FollowsByFollowerResource.js";
import { ListActivitiesResource } from "./resources/ListActivitiesResource.js";
import { ListFollowsResource } from "./resources/ListFollowsResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  Activity_skip_id_,
  Activity_skip_value_,
  Follow_skip_id_,
  Follow_skip_value_,
  User_skip_id_,
  User_skip_value_,
  Activity,
  Follow,
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
  readonly activities: InputDefinition<Activity_skip_id_, Activity_skip_value_>;
  readonly follows: InputDefinition<Follow_skip_id_, Follow_skip_value_>;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly followsByFollowerResource: ResourceClass<GraphCollections, Json>;
  readonly listActivitiesResource: ResourceClass<GraphCollections, Json>;
  readonly listFollowsResource: ResourceClass<GraphCollections, Json>;
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
      activities: new InputDefinition<Activity_skip_id_, Activity_skip_value_>(
        [],
      ),
      follows: new InputDefinition<Follow_skip_id_, Follow_skip_value_>([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      followsByFollowerResource: FollowsByFollowerResource,
      listActivitiesResource: ListActivitiesResource,
      listFollowsResource: ListFollowsResource,
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
