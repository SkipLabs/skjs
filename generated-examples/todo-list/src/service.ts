import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetTodoResource } from "./resources/GetTodoResource.js";
import { GetTodoStoredResource } from "./resources/GetTodoStoredResource.js";
import { ListTodosResource } from "./resources/ListTodosResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  Todo_skip_id_,
  Todo_skip_value_,
  User_skip_id_,
  User_skip_value_,
  GetTodoParams,
  ListTodosParams,
  Todo,
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
  readonly todos: InputDefinition<Todo_skip_id_, Todo_skip_value_>;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getTodoResource: ResourceClass<GraphCollections, GetTodoParams>;
  readonly getTodoStoredResource: ResourceClass<GraphCollections, Json>;
  readonly listTodosResource: ResourceClass<GraphCollections, ListTodosParams>;
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
      todos: new InputDefinition<Todo_skip_id_, Todo_skip_value_>([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      getTodoResource: GetTodoResource,
      getTodoStoredResource: GetTodoStoredResource,
      listTodosResource: ListTodosResource,
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
