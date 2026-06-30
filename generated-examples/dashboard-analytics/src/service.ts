import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetDashboardResource } from "./resources/GetDashboardResource.js";
import { GetMetricResource } from "./resources/GetMetricResource.js";
import { ListDashboardsByOwnerResource } from "./resources/ListDashboardsByOwnerResource.js";
import { ListMetricEventsByMetricResource } from "./resources/ListMetricEventsByMetricResource.js";
import { ListMetricsByOwnerResource } from "./resources/ListMetricsByOwnerResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  Dashboard_skip_id_,
  Dashboard_skip_value_,
  MetricEventKey,
  MetricEvent_skip_value_,
  Metric_skip_id_,
  Metric_skip_value_,
  User_skip_id_,
  User_skip_value_,
  Dashboard,
  MetricEvent,
  Metric,
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
  readonly dashboards: InputDefinition<
    Dashboard_skip_id_,
    Dashboard_skip_value_
  >;
  readonly metricEvents: InputDefinition<
    MetricEventKey,
    MetricEvent_skip_value_
  >;
  readonly metrics: InputDefinition<Metric_skip_id_, Metric_skip_value_>;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getDashboardResource: ResourceClass<GraphCollections, Json>;
  readonly getMetricResource: ResourceClass<GraphCollections, Json>;
  readonly listDashboardsByOwnerResource: ResourceClass<GraphCollections, Json>;
  readonly listMetricEventsByMetricResource: ResourceClass<
    GraphCollections,
    Json
  >;
  readonly listMetricsByOwnerResource: ResourceClass<GraphCollections, Json>;
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
      dashboards: new InputDefinition<
        Dashboard_skip_id_,
        Dashboard_skip_value_
      >([]),
      metricEvents: new InputDefinition<
        MetricEventKey,
        MetricEvent_skip_value_
      >([]),
      metrics: new InputDefinition<Metric_skip_id_, Metric_skip_value_>([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      getDashboardResource: GetDashboardResource,
      getMetricResource: GetMetricResource,
      listDashboardsByOwnerResource: ListDashboardsByOwnerResource,
      listMetricEventsByMetricResource: ListMetricEventsByMetricResource,
      listMetricsByOwnerResource: ListMetricsByOwnerResource,
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
