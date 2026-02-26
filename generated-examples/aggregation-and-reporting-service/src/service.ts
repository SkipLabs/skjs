import type {
  EagerCollection,
  Json,
  Resource,
  ResourceClass,
  SkipService,
  Context,
  Mapper,
  Reducer,
  Values,
  Nullable
} from "../skipruntime/core.js";
import { InputDefinition } from "../skipruntime/core.js";

import type {
  MetricId,
  MetricData,
  AggregatedMetricId,
  AggregatedMetricData,
  ReportId,
  ReportData,
  Period,
} from "./types.js";

export type MetricValue = {
  name: string;
  value: number;
  timestamp: number;
  tags: string;
};

export type BucketAccum = {
  count: number;
  sum: number;
  min: number;
  max: number;
};

export type AggregatedMetricValue = {
  metricName: string;
  period: Period;
  periodStart: number;
  count: number;
  sum: number;
  min: number;
  max: number;
  avg: number;
};

export type ReportValue = {
  metricName: string;
  period: Period;
  periodStart: number;
  periodEnd: number;
  totalCount: number;
  totalSum: number;
  overallMin: number;
  overallMax: number;
  overallAvg: number;
};

export type Inputs = {
  metrics: InputDefinition<MetricId, MetricData>;
};

export type InputCollections = {
  metrics: EagerCollection<MetricId, MetricData>;
};

export type GraphCollections = {
  metrics: EagerCollection<MetricId, MetricValue>;
  aggregatedMetrics: EagerCollection<AggregatedMetricId, AggregatedMetricValue>;
  reports: EagerCollection<ReportId, ReportValue>;
};

export type Resources = {
  "aggregatedMetrics-hourly": ResourceClass<GraphCollections, {}>;
  "aggregatedMetrics-daily": ResourceClass<GraphCollections, {}>;
  "aggregatedMetrics-weekly": ResourceClass<GraphCollections, {}>;
  "aggregatedMetrics-monthly": ResourceClass<GraphCollections, {}>;
  "reports-hourly": ResourceClass<GraphCollections, {}>;
  "reports-daily": ResourceClass<GraphCollections, {}>;
  "reports-weekly": ResourceClass<GraphCollections, {}>;
  "reports-monthly": ResourceClass<GraphCollections, {}>;
};

function getPeriodStart(timestamp: number, period: Period): number {
  const date = new Date(timestamp);
  if (period === "hour") {
    date.setUTCMinutes(0, 0, 0);
    return date.getTime();
  } else if (period === "day") {
    date.setUTCHours(0, 0, 0, 0);
    return date.getTime();
  } else if (period === "week") {
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

function getPeriodEnd(periodStart: number, period: Period): number {
  const date = new Date(periodStart);
  if (period === "hour") {
    date.setUTCHours(date.getUTCHours() + 1);
  } else if (period === "day") {
    date.setUTCDate(date.getUTCDate() + 1);
  } else if (period === "week") {
    date.setUTCDate(date.getUTCDate() + 7);
  } else {
    date.setUTCMonth(date.getUTCMonth() + 1);
  }
  return date.getTime();
}

export class MetricToBucketMapper implements Mapper<MetricId, MetricValue, [string, Period, number], number> {
  constructor() {}

  mapEntry(
    _key: MetricId,
    values: Values<MetricValue>,
    _context: Context
  ): Iterable<[[string, Period, number], number]> {
    const result: Array<[[string, Period, number], number]> = Array.of();
    const periods: Array<Period> = Array.of("hour", "day", "week", "month");
    for (const metric of values) {
      for (const period of periods) {
        const periodStart = getPeriodStart(metric.timestamp, period);
        const bucketKey: [string, Period, number] = [metric.name, period, periodStart];
        result.push([bucketKey, metric.value]);
      }
    }
    return result;
  }
}

export class BucketToAggregatedMetricMapper implements Mapper<[string, Period, number], BucketAccum, AggregatedMetricId, AggregatedMetricValue> {
  constructor() {}

  mapEntry(
    key: [string, Period, number],
    values: Values<BucketAccum>,
    _context: Context
  ): Iterable<[AggregatedMetricId, AggregatedMetricValue]> {
    const result: Array<[AggregatedMetricId, AggregatedMetricValue]> = Array.of();
    for (const accum of values) {
      const metricName = key[0];
      const period = key[1];
      const periodStart = key[2];
      const avg = accum.count > 0 ? accum.sum / accum.count : 0;
      const aggregatedMetricId: AggregatedMetricId = JSON.stringify(key);
      const aggregatedMetricValue: AggregatedMetricValue = {
        metricName: metricName,
        period: period,
        periodStart: periodStart,
        count: accum.count,
        sum: accum.sum,
        min: accum.min,
        max: accum.max,
        avg: avg
      };
      result.push([aggregatedMetricId, aggregatedMetricValue]);
    }
    return result;
  }
}

export class AggregatedMetricToReportMapper implements Mapper<AggregatedMetricId, AggregatedMetricValue, ReportId, ReportValue> {
  constructor() {}

  mapEntry(
    key: AggregatedMetricId,
    values: Values<AggregatedMetricValue>,
    _context: Context
  ): Iterable<[ReportId, ReportValue]> {
    const result: Array<[ReportId, ReportValue]> = Array.of();
    for (const agg of values) {
      const periodEnd = getPeriodEnd(agg.periodStart, agg.period);
      const reportValue: ReportValue = {
        metricName: agg.metricName,
        period: agg.period,
        periodStart: agg.periodStart,
        periodEnd: periodEnd,
        totalCount: agg.count,
        totalSum: agg.sum,
        overallMin: agg.min,
        overallMax: agg.max,
        overallAvg: agg.avg
      };
      result.push([key, reportValue]);
    }
    return result;
  }
}

export class FilterByPeriodAggregatedMetricMapper implements Mapper<AggregatedMetricId, AggregatedMetricValue, AggregatedMetricId, AggregatedMetricValue> {
  private period: Period;

  constructor(period: Period) {
    this.period = period;
  }

  mapEntry(
    key: AggregatedMetricId,
    values: Values<AggregatedMetricValue>,
    _context: Context
  ): Iterable<[AggregatedMetricId, AggregatedMetricValue]> {
    const result: Array<[AggregatedMetricId, AggregatedMetricValue]> = Array.of();
    for (const v of values) {
      if (v.period === this.period) {
        result.push([key, v]);
      }
    }
    return result;
  }
}

export class FilterByPeriodReportMapper implements Mapper<ReportId, ReportValue, ReportId, ReportValue> {
  private period: Period;

  constructor(period: Period) {
    this.period = period;
  }

  mapEntry(
    key: ReportId,
    values: Values<ReportValue>,
    _context: Context
  ): Iterable<[ReportId, ReportValue]> {
    const result: Array<[ReportId, ReportValue]> = Array.of();
    for (const v of values) {
      if (v.period === this.period) {
        result.push([key, v]);
      }
    }
    return result;
  }
}

export class BucketReducer implements Reducer<number, BucketAccum> {
  initial: Nullable<BucketAccum> = null;

  constructor() {}

  add(accum: Nullable<BucketAccum>, value: number): BucketAccum {
    if (accum === null) {
      return {
        count: 1,
        sum: value,
        min: value,
        max: value
      };
    }
    return {
      count: accum.count + 1,
      sum: accum.sum + value,
      min: value < accum.min ? value : accum.min,
      max: value > accum.max ? value : accum.max
    };
  }

  remove(_accum: BucketAccum, _value: number): Nullable<BucketAccum> {
    return null;
  }
}

export class AggregatedMetricsHourlyResource implements Resource<GraphCollections> {
  constructor(_params: {}) {}

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<AggregatedMetricId, AggregatedMetricData> {
    return cs.aggregatedMetrics.map(FilterByPeriodAggregatedMetricMapper, "hour");
  }
}

export class AggregatedMetricsDailyResource implements Resource<GraphCollections> {
  constructor(_params: {}) {}

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<AggregatedMetricId, AggregatedMetricData> {
    return cs.aggregatedMetrics.map(FilterByPeriodAggregatedMetricMapper, "day");
  }
}

export class AggregatedMetricsWeeklyResource implements Resource<GraphCollections> {
  constructor(_params: {}) {}

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<AggregatedMetricId, AggregatedMetricData> {
    return cs.aggregatedMetrics.map(FilterByPeriodAggregatedMetricMapper, "week");
  }
}

export class AggregatedMetricsMonthlyResource implements Resource<GraphCollections> {
  constructor(_params: {}) {}

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<AggregatedMetricId, AggregatedMetricData> {
    return cs.aggregatedMetrics.map(FilterByPeriodAggregatedMetricMapper, "month");
  }
}

export class ReportsHourlyResource implements Resource<GraphCollections> {
  constructor(_params: {}) {}

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<ReportId, ReportData> {
    return cs.reports.map(FilterByPeriodReportMapper, "hour");
  }
}

export class ReportsDailyResource implements Resource<GraphCollections> {
  constructor(_params: {}) {}

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<ReportId, ReportData> {
    return cs.reports.map(FilterByPeriodReportMapper, "day");
  }
}

export class ReportsWeeklyResource implements Resource<GraphCollections> {
  constructor(_params: {}) {}

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<ReportId, ReportData> {
    return cs.reports.map(FilterByPeriodReportMapper, "week");
  }
}

export class ReportsMonthlyResource implements Resource<GraphCollections> {
  constructor(_params: {}) {}

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<ReportId, ReportData> {
    return cs.reports.map(FilterByPeriodReportMapper, "month");
  }
}

class Service implements SkipService<Inputs, InputCollections, GraphCollections, Resources> {
  public inputs: Inputs;
  public resources: Resources;

  constructor() {
        this.inputs = { metrics: new InputDefinition<MetricId, MetricData>([]) };
    this.resources = {
      "aggregatedMetrics-hourly": AggregatedMetricsHourlyResource,
      "aggregatedMetrics-daily": AggregatedMetricsDailyResource,
      "aggregatedMetrics-weekly": AggregatedMetricsWeeklyResource,
      "aggregatedMetrics-monthly": AggregatedMetricsMonthlyResource,
      "reports-hourly": ReportsHourlyResource,
      "reports-daily": ReportsDailyResource,
      "reports-weekly": ReportsWeeklyResource,
      "reports-monthly": ReportsMonthlyResource
    };
  }

  createGraph(inputs: InputCollections, _context: Context): GraphCollections {
    const buckets = inputs.metrics.map(MetricToBucketMapper).reduce(BucketReducer);
    const aggregatedMetrics = buckets.map(BucketToAggregatedMetricMapper);
    const reports = aggregatedMetrics.map(AggregatedMetricToReportMapper);
    return {
      metrics: inputs.metrics,
      aggregatedMetrics: aggregatedMetrics,
      reports: reports
    };
  }
}

export function service(): SkipService<Inputs, InputCollections, GraphCollections, Resources> {
  return new Service();
}
