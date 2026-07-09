import type { Metric_skip_id_, Metric_skip_value_, Metric } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetMetricResourceInputs extends SharedCollections {
  readonly metrics: EagerCollection<Metric_skip_id_, Metric_skip_value_>;
}

export class GetMetricResource implements Resource<GetMetricResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetMetricResourceInputs,
    _context: Context,
  ): EagerCollection<Metric_skip_id_, Metric_skip_value_> {
    return inputs.metrics;
  }
}
