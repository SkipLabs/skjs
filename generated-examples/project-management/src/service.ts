import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetProjectResource } from "./resources/GetProjectResource.js";
import { GetProjectStoredResource } from "./resources/GetProjectStoredResource.js";
import { GetTaskResource } from "./resources/GetTaskResource.js";
import { GetTaskStoredResource } from "./resources/GetTaskStoredResource.js";
import { GetUserResource } from "./resources/GetUserResource.js";
import { ListProjectTasksResource } from "./resources/ListProjectTasksResource.js";
import { ListProjectsResource } from "./resources/ListProjectsResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  Project_skip_id_,
  Project_skip_value_,
  Task_skip_id_,
  Task_skip_value_,
  User_skip_id_,
  User_skip_value_,
  GetProjectParams,
  GetTaskParams,
  GetUserParams,
  ListTasksParams,
  ListProjectsParams,
  Project,
  Task,
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
  readonly projects: InputDefinition<Project_skip_id_, Project_skip_value_>;
  readonly tasks: InputDefinition<Task_skip_id_, Task_skip_value_>;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getProjectResource: ResourceClass<
    GraphCollections,
    GetProjectParams
  >;
  readonly getProjectStoredResource: ResourceClass<GraphCollections, Json>;
  readonly getTaskResource: ResourceClass<GraphCollections, GetTaskParams>;
  readonly getTaskStoredResource: ResourceClass<GraphCollections, Json>;
  readonly getUserResource: ResourceClass<GraphCollections, GetUserParams>;
  readonly listProjectTasksResource: ResourceClass<
    GraphCollections,
    ListTasksParams
  >;
  readonly listProjectsResource: ResourceClass<
    GraphCollections,
    ListProjectsParams
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
      projects: new InputDefinition<Project_skip_id_, Project_skip_value_>([]),
      tasks: new InputDefinition<Task_skip_id_, Task_skip_value_>([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      getProjectResource: GetProjectResource,
      getProjectStoredResource: GetProjectStoredResource,
      getTaskResource: GetTaskResource,
      getTaskStoredResource: GetTaskStoredResource,
      getUserResource: GetUserResource,
      listProjectTasksResource: ListProjectTasksResource,
      listProjectsResource: ListProjectsResource,
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
