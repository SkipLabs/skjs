import type {
  Dashboard_skip_id_,
  Dashboard,
  Dashboard_skip_value_,
  MetricEventKey,
  MetricEvent_skip_value_,
  MetricEvent,
  Metric_skip_id_,
  Metric,
  Metric_skip_value_,
  User_skip_id_,
  User,
  User_skip_value_,
} from "./types.js";
import type {
  EagerCollection,
  Context,
  NamedEagerCollections,
  SharedCollections,
} from "@skipruntime/core";

export interface InputCollections extends NamedEagerCollections {
  readonly dashboards: EagerCollection<
    Dashboard_skip_id_,
    Dashboard_skip_value_
  >;
  readonly metricEvents: EagerCollection<
    MetricEventKey,
    MetricEvent_skip_value_
  >;
  readonly metrics: EagerCollection<Metric_skip_id_, Metric_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export interface GraphCollections extends SharedCollections {
  readonly dashboards: EagerCollection<
    Dashboard_skip_id_,
    Dashboard_skip_value_
  >;
  readonly metricEvents: EagerCollection<
    MetricEventKey,
    MetricEvent_skip_value_
  >;
  readonly metrics: EagerCollection<Metric_skip_id_, Metric_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const output_dashboards = inputs.dashboards;
  const output_metricEvents = inputs.metricEvents;
  const output_metrics = inputs.metrics;
  const output_users = inputs.users;
  return {
    dashboards: output_dashboards,
    metricEvents: output_metricEvents,
    metrics: output_metrics,
    users: output_users,
  };
}
