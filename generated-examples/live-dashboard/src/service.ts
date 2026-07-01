import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetDashboardResource } from "./resources/GetDashboardResource.js";
import { GetMetricResource } from "./resources/GetMetricResource.js";
import { GetWidgetResource } from "./resources/GetWidgetResource.js";
import { ListDashboardsResource } from "./resources/ListDashboardsResource.js";
import { ListMetricPointsResource } from "./resources/ListMetricPointsResource.js";
import { ListMetricsResource } from "./resources/ListMetricsResource.js";
import { MetricStatsResource } from "./resources/MetricStatsResource.js";
import { WidgetsByDashboardResource } from "./resources/WidgetsByDashboardResource.js";
import { WidgetsByMetricResource } from "./resources/WidgetsByMetricResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  Dashboard_skip_id_,
  DashboardStored,
  MetricPointCompositeKey,
  MetricPointValue,
  Metric_skip_id_,
  MetricStored,
  User_skip_id_,
  UserStored,
  Widget_skip_id_,
  Widget_skip_value_,
  ListDashboardsParams,
  ListMetricPointsParams,
  ListMetricsParams,
  Dashboard,
  Metric,
  User,
  Widget,
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
  readonly dashboards: InputDefinition<Dashboard_skip_id_, DashboardStored>;
  readonly metricPoints: InputDefinition<
    MetricPointCompositeKey,
    MetricPointValue
  >;
  readonly metrics: InputDefinition<Metric_skip_id_, MetricStored>;
  readonly users: InputDefinition<User_skip_id_, UserStored>;
  readonly widgets: InputDefinition<Widget_skip_id_, Widget_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getDashboardResource: ResourceClass<GraphCollections, Json>;
  readonly getMetricResource: ResourceClass<GraphCollections, Json>;
  readonly getWidgetResource: ResourceClass<GraphCollections, Json>;
  readonly listDashboardsResource: ResourceClass<
    GraphCollections,
    ListDashboardsParams
  >;
  readonly listMetricPointsResource: ResourceClass<
    GraphCollections,
    ListMetricPointsParams
  >;
  readonly listMetricsResource: ResourceClass<
    GraphCollections,
    ListMetricsParams
  >;
  readonly metricStatsResource: ResourceClass<GraphCollections, Json>;
  readonly widgetsByDashboardResource: ResourceClass<GraphCollections, Json>;
  readonly widgetsByMetricResource: ResourceClass<GraphCollections, Json>;
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
      dashboards: new InputDefinition<Dashboard_skip_id_, DashboardStored>([]),
      metricPoints: new InputDefinition<
        MetricPointCompositeKey,
        MetricPointValue
      >([]),
      metrics: new InputDefinition<Metric_skip_id_, MetricStored>([]),
      users: new InputDefinition<User_skip_id_, UserStored>([]),
      widgets: new InputDefinition<Widget_skip_id_, Widget_skip_value_>([]),
    };
    this.resources = {
      getDashboardResource: GetDashboardResource,
      getMetricResource: GetMetricResource,
      getWidgetResource: GetWidgetResource,
      listDashboardsResource: ListDashboardsResource,
      listMetricPointsResource: ListMetricPointsResource,
      listMetricsResource: ListMetricsResource,
      metricStatsResource: MetricStatsResource,
      widgetsByDashboardResource: WidgetsByDashboardResource,
      widgetsByMetricResource: WidgetsByMetricResource,
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
