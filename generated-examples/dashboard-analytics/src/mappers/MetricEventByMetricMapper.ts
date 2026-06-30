import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  MetricEventKey,
  MetricEvent_skip_value_,
  Metric_skip_id_,
  MetricEvent,
  Metric,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each metric event entry, emit one output pair whose key is sourced from the entry's key's metricId field (a Metric primary key) and whose value lists every required field of MetricEvent explicitly — id sourced from the entry's key's id field; metricId sourced from the entry's key's metricId field; ownerId sourced from the entry's value; value sourced from the entry's value; occurredAt sourced from the entry's value; createdAt sourced from the entry's value; and the optional tags field with an explicit presence clause: present when the entry's value's tags field is present, sourced from the entry's value, absent otherwise. The original event id is preserved in the value (sourced from the entry's key's id field) so downstream consumers can reconstruct full events keyed by metricId.
export class MetricEventByMetricMapper implements Mapper<
  MetricEventKey,
  MetricEvent_skip_value_,
  Metric_skip_id_,
  MetricEvent
> {
  mapEntry(
    key: MetricEventKey,
    values: Values<MetricEvent_skip_value_>,
    context: Context,
  ): Iterable<[Metric_skip_id_, MetricEvent]> {
    // > body
    const emits: [Metric_skip_id_, MetricEvent][] = [];
    for (const value of values.toArray()) {
      const event: MetricEvent = {
        id: key.id,
        metricId: key.metricId,
        ownerId: value.ownerId,
        value: value.value,
        occurredAt: value.occurredAt,
        createdAt: value.createdAt,
        ...(value.tags !== undefined && { tags: value.tags }),
      };
      emits.push([key.metricId, event]);
    }
    return emits;
    // < body
  }
}
