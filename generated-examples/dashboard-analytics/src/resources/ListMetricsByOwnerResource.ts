import { MetricByOwnerWithIdMapper } from "../mappers/MetricByOwnerWithIdMapper.js";
import type {
  Metric_skip_id_,
  Metric_skip_value_,
  User_skip_id_,
  Metric,
  User,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListMetricsByOwnerResourceInputs extends SharedCollections {
  readonly metrics: EagerCollection<Metric_skip_id_, Metric_skip_value_>;
}

export class ListMetricsByOwnerResource implements Resource<ListMetricsByOwnerResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: ListMetricsByOwnerResourceInputs,
    _context: Context,
  ): EagerCollection<User_skip_id_, Metric> {
    const metricsByOwner = inputs.metrics.map(MetricByOwnerWithIdMapper);
    return metricsByOwner;
  }
}
