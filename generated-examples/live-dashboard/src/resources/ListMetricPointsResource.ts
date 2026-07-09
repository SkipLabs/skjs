import { FilterMetricPointsByMetricMapper } from "../mappers/FilterMetricPointsByMetricMapper.js";
import type {
  MetricPointCompositeKey,
  MetricPointValue,
  ListMetricPointsParams,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListMetricPointsResourceInputs extends SharedCollections {
  readonly metricPoints: EagerCollection<
    MetricPointCompositeKey,
    MetricPointValue
  >;
}

export class ListMetricPointsResource implements Resource<ListMetricPointsResourceInputs> {
  private readonly metricId: string;

  constructor(params: ListMetricPointsParams) {
    this.metricId = params.metricId;
  }

  instantiate(
    inputs: ListMetricPointsResourceInputs,
    _context: Context,
  ): EagerCollection<MetricPointCompositeKey, MetricPointValue> {
    return inputs.metricPoints.map(
      FilterMetricPointsByMetricMapper,
      this.metricId,
    );
  }
}
