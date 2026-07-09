import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { Metric_skip_id_, Metric_skip_value_, Metric } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each metric entry, emit the entry unchanged when the entry's ownerId field equals the userId param. Otherwise emit nothing.
export class MetricsForOwnerMapper implements Mapper<
  Metric_skip_id_,
  Metric_skip_value_,
  Metric_skip_id_,
  Metric_skip_value_
> {
  constructor(private userId: string) {}

  mapEntry(
    key: Metric_skip_id_,
    values: Values<Metric_skip_value_>,
    context: Context,
  ): Iterable<[Metric_skip_id_, Metric_skip_value_]> {
    // > body
    const emits: [Metric_skip_id_, Metric_skip_value_][] = [];
    for (const value of values.toArray()) {
      if (value.ownerId === this.userId) {
        emits.push([key, value]);
      }
    }
    return emits;
    // < body
  }
}
