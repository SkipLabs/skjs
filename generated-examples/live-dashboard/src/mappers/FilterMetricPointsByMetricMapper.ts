import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { MetricPointCompositeKey, MetricPointValue } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each metric point entry, when the entry's key's metricId field equals the metricId param, emit the entry unchanged. Otherwise emit nothing.
export class FilterMetricPointsByMetricMapper implements Mapper<
  MetricPointCompositeKey,
  MetricPointValue,
  MetricPointCompositeKey,
  MetricPointValue
> {
  constructor(private metricId: string) {}

  mapEntry(
    key: MetricPointCompositeKey,
    values: Values<MetricPointValue>,
    context: Context,
  ): Iterable<[MetricPointCompositeKey, MetricPointValue]> {
    // > body
    const emits: [MetricPointCompositeKey, MetricPointValue][] = [];
    if (key.metricId === this.metricId) {
      for (const value of values.toArray()) {
        emits.push([key, value]);
      }
    }
    return emits;
    // < body
  }
}
