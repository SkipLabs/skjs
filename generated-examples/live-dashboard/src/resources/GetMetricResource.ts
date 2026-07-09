import type { Metric_skip_id_, MetricStored, Metric } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetMetricResourceInputs extends SharedCollections {
  readonly metrics: EagerCollection<Metric_skip_id_, MetricStored>;
}

export class GetMetricResource implements Resource<GetMetricResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetMetricResourceInputs,
    _context: Context,
  ): EagerCollection<Metric_skip_id_, MetricStored> {
    return inputs.metrics;
  }
}
