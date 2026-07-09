import { MetricsForOwnerMapper } from "../mappers/MetricsForOwnerMapper.js";
import type {
  Metric_skip_id_,
  Metric_skip_value_,
  ListMetricsParams,
  Metric,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListMetricsResourceInputs extends SharedCollections {
  readonly metrics: EagerCollection<Metric_skip_id_, Metric_skip_value_>;
}

export class ListMetricsResource implements Resource<ListMetricsResourceInputs> {
  private readonly userId: string;

  constructor(params: ListMetricsParams) {
    this.userId = params.userId;
  }

  instantiate(
    inputs: ListMetricsResourceInputs,
    _context: Context,
  ): EagerCollection<Metric_skip_id_, Metric_skip_value_> {
    return inputs.metrics.map(MetricsForOwnerMapper, this.userId);
  }
}
