import type {
  Dashboard_skip_id_,
  Dashboard,
  DashboardStored,
  MetricPointCompositeKey,
  MetricPointValue,
  Metric_skip_id_,
  Metric,
  MetricStored,
  User_skip_id_,
  User,
  UserStored,
  Widget_skip_id_,
  Widget,
  Widget_skip_value_,
} from "./types.js";
import type {
  EagerCollection,
  Context,
  NamedEagerCollections,
  SharedCollections,
} from "@skipruntime/core";

export interface InputCollections extends NamedEagerCollections {
  readonly dashboards: EagerCollection<Dashboard_skip_id_, DashboardStored>;
  readonly metricPoints: EagerCollection<
    MetricPointCompositeKey,
    MetricPointValue
  >;
  readonly metrics: EagerCollection<Metric_skip_id_, MetricStored>;
  readonly users: EagerCollection<User_skip_id_, UserStored>;
  readonly widgets: EagerCollection<Widget_skip_id_, Widget_skip_value_>;
}

export interface GraphCollections extends SharedCollections {
  readonly dashboards: EagerCollection<Dashboard_skip_id_, DashboardStored>;
  readonly metricPoints: EagerCollection<
    MetricPointCompositeKey,
    MetricPointValue
  >;
  readonly metrics: EagerCollection<Metric_skip_id_, MetricStored>;
  readonly users: EagerCollection<User_skip_id_, UserStored>;
  readonly widgets: EagerCollection<Widget_skip_id_, Widget_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const output_dashboards = inputs.dashboards;
  const output_metricPoints = inputs.metricPoints;
  const output_metrics = inputs.metrics;
  const output_users = inputs.users;
  const output_widgets = inputs.widgets;
  return {
    dashboards: output_dashboards,
    metricPoints: output_metricPoints,
    metrics: output_metrics,
    users: output_users,
    widgets: output_widgets,
  };
}
