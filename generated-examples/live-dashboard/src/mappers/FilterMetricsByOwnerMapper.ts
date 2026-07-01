import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { Metric_skip_id_, MetricStored, Metric } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each metric entry, when the entry's value's ownerId field equals the userId param, emit the entry unchanged. Otherwise emit nothing.
export class FilterMetricsByOwnerMapper implements Mapper<
  Metric_skip_id_,
  MetricStored,
  Metric_skip_id_,
  MetricStored
> {
  constructor(private userId: string) {}

  mapEntry(
    key: Metric_skip_id_,
    values: Values<MetricStored>,
    context: Context,
  ): Iterable<[Metric_skip_id_, MetricStored]> {
    // > body
    const emits: [Metric_skip_id_, MetricStored][] = [];
    for (const value of values.toArray()) {
      if (value.ownerId === this.userId) {
        emits.push([key, value]);
      }
    }
    return emits;
    // < body
  }
}
