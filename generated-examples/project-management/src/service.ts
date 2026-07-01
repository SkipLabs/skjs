import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetProjectResource } from "./resources/GetProjectResource.js";
import { GetTaskResource } from "./resources/GetTaskResource.js";
import { GetUserResource } from "./resources/GetUserResource.js";
import { ListProjectsByOwnerResource } from "./resources/ListProjectsByOwnerResource.js";
import { ListTasksByProjectResource } from "./resources/ListTasksByProjectResource.js";
import type {
  Project_skip_id_,
  Project_skip_value_,
  Task_skip_id_,
  Task_skip_value_,
  User_skip_id_,
  User_skip_value_,
  ListProjectsParams,
  ListProjectTasksParams,
  Project,
  Task,
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
  readonly projects: InputDefinition<Project_skip_id_, Project_skip_value_>;
  readonly tasks: InputDefinition<Task_skip_id_, Task_skip_value_>;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getProjectResource: ResourceClass<GraphCollections, Json>;
  readonly getTaskResource: ResourceClass<GraphCollections, Json>;
  readonly getUserResource: ResourceClass<GraphCollections, Json>;
  readonly listProjectsByOwnerResource: ResourceClass<
    GraphCollections,
    ListProjectsParams
  >;
  readonly listTasksByProjectResource: ResourceClass<
    GraphCollections,
    ListProjectTasksParams
  >;
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
      projects: new InputDefinition<Project_skip_id_, Project_skip_value_>([]),
      tasks: new InputDefinition<Task_skip_id_, Task_skip_value_>([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      getProjectResource: GetProjectResource,
      getTaskResource: GetTaskResource,
      getUserResource: GetUserResource,
      listProjectsByOwnerResource: ListProjectsByOwnerResource,
      listTasksByProjectResource: ListTasksByProjectResource,
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
