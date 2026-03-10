import type {
  EagerCollection,

  Resource,
  ResourceClass,
  SkipService,
  Context,
  Mapper,
  Reducer,
  Values,
  Nullable,
  DepSafe
} from "../skipruntime/core.js";
import { InputDefinition } from "../skipruntime/core.js";


import type {
  MetricId,
  MetricValue,
  AggregatedMetricId,
  AggregatedMetricValue,
  Period
} from "./types.js";

export type AggregatedData = {
  count: number;
  sum: number;
};

// Using object instead of tuple as readonly tuples are not yet supported by skjs.
export type BucketKey = {
  metricName: string;
  period: Period;
  periodStart: number;
};

export type Inputs = {
  metrics: InputDefinition<MetricId, MetricValue>;
};

export type InputCollections = {
  metrics: EagerCollection<MetricId, MetricValue>;
};

export type GraphCollections = {
  metrics: EagerCollection<MetricId, MetricValue>;
};

export type Resources = {
  readonly "stats-hourly": ResourceClass<GraphCollections, {}>;
  readonly "stats-daily": ResourceClass<GraphCollections, {}>;
  readonly "stats-weekly": ResourceClass<GraphCollections, {}>;
  readonly "stats-monthly": ResourceClass<GraphCollections, {}>;
};

export class MetricToBucketMapper implements Mapper<MetricId, MetricValue, BucketKey, number> {
  private period: Period;

  constructor(period: Period) {
    this.period = period;
  }

  mapEntry(
    _key: MetricId,
    values: Values<MetricValue>,
    _context: Context
  ): Iterable<[BucketKey, number]> {
    const result: Array<[BucketKey, number]> = Array.of();
    for (const v of values) {
      const periodStart = this.computePeriodStart(v.timestamp);
      const bucketKey: BucketKey = { metricName: v.name, period: this.period, periodStart: periodStart };
      result.push([bucketKey, v.value]);
    }
    return result;
  }

  computePeriodStart(timestamp: number): number {
    const date = new Date(timestamp);
    if (this.period === "hour") {
      date.setUTCMinutes(0, 0, 0);
      return date.getTime();
    } else if (this.period === "day") {
      date.setUTCHours(0, 0, 0, 0);
      return date.getTime();
    } else if (this.period === "week") {
      date.setUTCHours(0, 0, 0, 0);
      const dayOfWeek = date.getUTCDay();
      const diff = dayOfWeek === 0 ? 6 : dayOfWeek - 1;
      date.setUTCDate(date.getUTCDate() - diff);
      return date.getTime();
    } else {
      date.setUTCHours(0, 0, 0, 0);
      date.setUTCDate(1);
      return date.getTime();
    }
  }
}

export class BucketToAggregatedMetricMapper implements Mapper<BucketKey, AggregatedData, AggregatedMetricId, AggregatedMetricValue> {
  constructor() {
  }

  mapEntry(
    key: BucketKey,
    values: Values<AggregatedData>,
    _context: Context
  ): Iterable<[AggregatedMetricId, AggregatedMetricValue]> {
    const result: Array<[AggregatedMetricId, AggregatedMetricValue]> = Array.of();
    for (const v of values) {
      const metricName = key.metricName;
      const period = key.period;
      const periodStart = key.periodStart;
      const avg = v.count > 0 ? v.sum / v.count : 0;
      const aggregatedId: AggregatedMetricId = JSON.stringify(key);
      const aggregatedValue: AggregatedMetricValue = {
        metricName: metricName,
        period: period,
        periodStart: periodStart,
        count: v.count,
        sum: v.sum,
        avg: avg
      };
      result.push([aggregatedId, aggregatedValue]);
    }
    return result;
  }
}

export class FilterByMetricNameMapper implements Mapper<AggregatedMetricId, AggregatedMetricValue, AggregatedMetricId, AggregatedMetricValue> {
  private metricName: string;

  constructor(metricName: string) {
    this.metricName = metricName;
  }

  mapEntry(
    key: AggregatedMetricId,
    values: Values<AggregatedMetricValue>,
    _context: Context
  ): Iterable<[AggregatedMetricId, AggregatedMetricValue]> {
    const result: Array<[AggregatedMetricId, AggregatedMetricValue]> = Array.of();
    for (const v of values) {
      if (v.metricName === this.metricName) {
        result.push([key, v]);
      }
    }
    return result;
  }
}

export class MetricAggregationReducer implements Reducer<number, AggregatedData> {
  initial: Nullable<AggregatedData> = null;

  constructor() {
  }

  add(accum: Nullable<AggregatedData>, value: number & DepSafe): AggregatedData {
    if (accum === null) {
      return { count: 1, sum: value };
    }
    return { count: accum.count + 1, sum: accum.sum + value };
  }

  remove(accum: AggregatedData, value: number & DepSafe): Nullable<AggregatedData> {
    const newCount = accum.count - 1;
    const newSum = accum.sum - value;
    if (newCount <= 0) {
      return null;
    }
    return { count: newCount, sum: newSum };
  }
}

export class StatsHourlyResource implements Resource<GraphCollections> {
  private metricName: string | null;

  constructor(params: { metricName?: string } = {}) {
    this.metricName = params.metricName ?? null;
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<AggregatedMetricId, AggregatedMetricValue> {
    const period: Period = "hour";
    const bucketed = cs.metrics.map(MetricToBucketMapper, period);
    const aggregated = bucketed.reduce(MetricAggregationReducer);
    const formatted = aggregated.map(BucketToAggregatedMetricMapper);
    if (this.metricName !== null) {
      return formatted.map(FilterByMetricNameMapper, this.metricName);
    }
    return formatted;
  }
}

export class StatsDailyResource implements Resource<GraphCollections> {
  private metricName: string | null;

  constructor(params: { metricName?: string } = {}) {
    this.metricName = params.metricName ?? null;
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<AggregatedMetricId, AggregatedMetricValue> {
    const period: Period = "day";
    const bucketed = cs.metrics.map(MetricToBucketMapper, period);
    const aggregated = bucketed.reduce(MetricAggregationReducer);
    const formatted = aggregated.map(BucketToAggregatedMetricMapper);
    if (this.metricName !== null) {
      return formatted.map(FilterByMetricNameMapper, this.metricName);
    }
    return formatted;
  }
}

export class StatsWeeklyResource implements Resource<GraphCollections> {
  private metricName: string | null;

  constructor(params: { metricName?: string } = {}) {
    this.metricName = params.metricName ?? null;
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<AggregatedMetricId, AggregatedMetricValue> {
    const period: Period = "week";
    const bucketed = cs.metrics.map(MetricToBucketMapper, period);
    const aggregated = bucketed.reduce(MetricAggregationReducer);
    const formatted = aggregated.map(BucketToAggregatedMetricMapper);
    if (this.metricName !== null) {
      return formatted.map(FilterByMetricNameMapper, this.metricName);
    }
    return formatted;
  }
}

export class StatsMonthlyResource implements Resource<GraphCollections> {
  private metricName: string | null;

  constructor(params: { metricName?: string } = {}) {
    this.metricName = params.metricName ?? null;
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<AggregatedMetricId, AggregatedMetricValue> {
    const period: Period = "month";
    const bucketed = cs.metrics.map(MetricToBucketMapper, period);
    const aggregated = bucketed.reduce(MetricAggregationReducer);
    const formatted = aggregated.map(BucketToAggregatedMetricMapper);
    if (this.metricName !== null) {
      return formatted.map(FilterByMetricNameMapper, this.metricName);
    }
    return formatted;
  }
}

class Service implements SkipService<Inputs, InputCollections, GraphCollections> {
  public readonly inputs: Inputs;
  public readonly resources: Resources;

  constructor() {
        this.inputs = { metrics: new InputDefinition<MetricId, MetricValue>([]) };
    this.resources = {
      "stats-hourly": StatsHourlyResource,
      "stats-daily": StatsDailyResource,
      "stats-weekly": StatsWeeklyResource,
      "stats-monthly": StatsMonthlyResource
    };
  }

  createGraph(inputs: InputCollections, _context: Context): GraphCollections {
    return { metrics: inputs.metrics };
  }
}

export function service(): SkipService<Inputs, InputCollections, GraphCollections> {
  return new Service();
}
