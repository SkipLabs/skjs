import { MetricPointByMetricMapper } from "../mappers/MetricPointByMetricMapper.js";
import { MetricStatsMapper } from "../mappers/MetricStatsMapper.js";
import type {
  MetricPointCompositeKey,
  MetricPointValue,
  Metric_skip_id_,
  MetricStats,
  Metric,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface MetricStatsResourceInputs extends SharedCollections {
  readonly metricPoints: EagerCollection<
    MetricPointCompositeKey,
    MetricPointValue
  >;
}

export class MetricStatsResource implements Resource<MetricStatsResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: MetricStatsResourceInputs,
    _context: Context,
  ): EagerCollection<Metric_skip_id_, MetricStats> {
    const pointsByMetric = inputs.metricPoints.map(MetricPointByMetricMapper);
    return pointsByMetric.map(MetricStatsMapper);
  }
}
