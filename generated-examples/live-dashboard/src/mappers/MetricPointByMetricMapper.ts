import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  MetricPointCompositeKey,
  MetricPointValue,
  Metric_skip_id_,
  MetricPoint,
  Metric,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each metric point entry, emit one output pair whose key is sourced from the entry's key metricId field (a Metric id) and whose value is a MetricPoint record listing every required field explicitly: metricId sourced from the entry's key metricId field; timestamp sourced from the entry's key timestamp field; value sourced from the entry's value's value field; labels is present when the entry's value's labels field is present, sourced from the entry's value's labels field, absent otherwise.
export class MetricPointByMetricMapper implements Mapper<
  MetricPointCompositeKey,
  MetricPointValue,
  Metric_skip_id_,
  MetricPoint
> {
  mapEntry(
    key: MetricPointCompositeKey,
    values: Values<MetricPointValue>,
    context: Context,
  ): Iterable<[Metric_skip_id_, MetricPoint]> {
    // > body
    const emits: [Metric_skip_id_, MetricPoint][] = [];
    for (const value of values.toArray()) {
      const point: MetricPoint = {
        metricId: key.metricId,
        timestamp: key.timestamp,
        value: value.value,
        ...(value.labels !== undefined && { labels: value.labels }),
      };
      emits.push([key.metricId, point]);
    }
    return emits;
    // < body
  }
}
