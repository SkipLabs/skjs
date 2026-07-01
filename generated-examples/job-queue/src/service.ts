import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetJobResource } from "./resources/GetJobResource.js";
import { ListJobsResource } from "./resources/ListJobsResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  Job_skip_id_,
  Job_skip_value_,
  User_skip_id_,
  User_skip_value_,
  ListJobsParams,
  Job,
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
  readonly jobs: InputDefinition<Job_skip_id_, Job_skip_value_>;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getJobResource: ResourceClass<GraphCollections, Json>;
  readonly listJobsResource: ResourceClass<GraphCollections, ListJobsParams>;
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
      jobs: new InputDefinition<Job_skip_id_, Job_skip_value_>([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      getJobResource: GetJobResource,
      listJobsResource: ListJobsResource,
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
