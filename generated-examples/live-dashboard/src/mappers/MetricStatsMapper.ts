import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Metric_skip_id_,
  MetricPoint,
  MetricStats,
  Metric,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each entry (keyed by metricId), receive all MetricPoint values associated with that metricId. Compute: pointCount as the number of values; sum as the arithmetic sum of every value's value field; minValue as the numeric minimum of every value's value field; maxValue as the numeric maximum of every value's value field; lastTimestamp as the lexicographically greatest timestamp string across all values (ISO 8601 lexicographic ordering matches chronological ordering when timestamps use the same zone offset); lastValue as the value field of the value whose timestamp equals lastTimestamp. When two or more values share the same lastTimestamp, break the tie by picking the value with the numerically greatest `value` field; if that also ties, pick the value with the lexicographically greatest `metricId` field (note: within one entry all values share the same metricId, so this final key is a total-order stub that never actually differs — the (timestamp, value) pair is the effective total order). Emit one output pair whose key is the entry's key unchanged and whose value is a MetricStats record where pointCount is required and set to the count; lastValue is present when pointCount is strictly greater than zero, sourced from lastValue as computed above, absent otherwise; lastTimestamp is present when pointCount is strictly greater than zero, sourced from lastTimestamp as computed above, absent otherwise; minValue is present when pointCount is strictly greater than zero, sourced from minValue as computed above, absent otherwise; maxValue is present when pointCount is strictly greater than zero, sourced from maxValue as computed above, absent otherwise; avgValue is present when pointCount is strictly greater than zero, sourced from sum divided by pointCount, absent otherwise. On the empty-values case (no points), emit one entry with pointCount zero and every other field absent.
export class MetricStatsMapper implements Mapper<
  Metric_skip_id_,
  MetricPoint,
  Metric_skip_id_,
  MetricStats
> {
  mapEntry(
    key: Metric_skip_id_,
    values: Values<MetricPoint>,
    context: Context,
  ): Iterable<[Metric_skip_id_, MetricStats]> {
    // > body
    const arr = values.toArray();
    const pointCount = arr.length;
    if (pointCount === 0) {
      const stats: MetricStats = { pointCount: 0 };
      return [[key, stats]];
    }
    let sum = 0;
    let minValue = arr[0]!.value;
    let maxValue = arr[0]!.value;
    let lastTimestamp = arr[0]!.timestamp;
    let lastValue = arr[0]!.value;
    let lastMetricId = arr[0]!.metricId;
    for (let i = 0; i < arr.length; i++) {
      const p = arr[i]!;
      sum += p.value;
      if (p.value < minValue) minValue = p.value;
      if (p.value > maxValue) maxValue = p.value;
      if (i === 0) continue;
      if (
        p.timestamp > lastTimestamp ||
        (p.timestamp === lastTimestamp && p.value > lastValue) ||
        (p.timestamp === lastTimestamp &&
          p.value === lastValue &&
          p.metricId > lastMetricId)
      ) {
        lastTimestamp = p.timestamp;
        lastValue = p.value;
        lastMetricId = p.metricId;
      }
    }
    const avgValue = sum / pointCount;
    const stats: MetricStats = {
      pointCount,
      lastValue,
      lastTimestamp,
      minValue,
      maxValue,
      avgValue,
    };
    return [[key, stats]];
    // < body
  }
}
