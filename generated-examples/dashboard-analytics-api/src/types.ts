export type MetricId = string;

export type MetricValue = {
  name: string;
  value: number;
  timestamp: number;
};

export type Metric = {
  id: MetricId;
  name: string;
  value: number;
  timestamp: number;
};

export type Period = "hour" | "day" | "week" | "month";

export type AggregatedMetricId = string;

export type AggregatedMetricValue = {
  metricName: string;
  period: Period;
  periodStart: number;
  count: number;
  sum: number;
  avg: number;
};

export type AggregatedMetric = {
  id: AggregatedMetricId;
  metricName: string;
  period: Period;
  periodStart: number;
  count: number;
  sum: number;
  avg: number;
};
