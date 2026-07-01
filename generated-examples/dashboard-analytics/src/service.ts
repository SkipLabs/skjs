import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetMetricResource } from "./resources/GetMetricResource.js";
import { ListMetricsResource } from "./resources/ListMetricsResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  Metric_skip_id_,
  Metric_skip_value_,
  User_skip_id_,
  User_skip_value_,
  ListMetricsParams,
  Metric,
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
  readonly metrics: InputDefinition<Metric_skip_id_, Metric_skip_value_>;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getMetricResource: ResourceClass<GraphCollections, Json>;
  readonly listMetricsResource: ResourceClass<
    GraphCollections,
    ListMetricsParams
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
      metrics: new InputDefinition<Metric_skip_id_, Metric_skip_value_>([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      getMetricResource: GetMetricResource,
      listMetricsResource: ListMetricsResource,
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
