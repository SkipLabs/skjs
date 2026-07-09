import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetJobResource } from "./resources/GetJobResource.js";
import { ListJobsForQueueResource } from "./resources/ListJobsForQueueResource.js";
import { QueuesResource } from "./resources/QueuesResource.js";
import { RunningJobCountByQueueResource } from "./resources/RunningJobCountByQueueResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  Job_skip_id_,
  Job_skip_value_,
  Queue_skip_id_,
  Queue_skip_value_,
  User_skip_id_,
  User_skip_value_,
  ListJobsForQueueParams,
  Job,
  Queue,
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
  readonly jobs: InputDefinition<Job_skip_id_, Job_skip_value_>;
  readonly queues: InputDefinition<Queue_skip_id_, Queue_skip_value_>;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getJobResource: ResourceClass<GraphCollections, Json>;
  readonly listJobsForQueueResource: ResourceClass<
    GraphCollections,
    ListJobsForQueueParams
  >;
  readonly queuesResource: ResourceClass<GraphCollections, Json>;
  readonly runningJobCountByQueueResource: ResourceClass<
    GraphCollections,
    Json
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
      jobs: new InputDefinition<Job_skip_id_, Job_skip_value_>([]),
      queues: new InputDefinition<Queue_skip_id_, Queue_skip_value_>([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      getJobResource: GetJobResource,
      listJobsForQueueResource: ListJobsForQueueResource,
      queuesResource: QueuesResource,
      runningJobCountByQueueResource: RunningJobCountByQueueResource,
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
