import { MetricEventByMetricMapper } from "../mappers/MetricEventByMetricMapper.js";
import type {
  MetricEventKey,
  MetricEvent_skip_value_,
  Metric_skip_id_,
  MetricEvent,
  Metric,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListMetricEventsByMetricResourceInputs extends SharedCollections {
  readonly metricEvents: EagerCollection<
    MetricEventKey,
    MetricEvent_skip_value_
  >;
}

export class ListMetricEventsByMetricResource implements Resource<ListMetricEventsByMetricResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: ListMetricEventsByMetricResourceInputs,
    _context: Context,
  ): EagerCollection<Metric_skip_id_, MetricEvent> {
    const eventsByMetric = inputs.metricEvents.map(MetricEventByMetricMapper);
    return eventsByMetric;
  }
}
