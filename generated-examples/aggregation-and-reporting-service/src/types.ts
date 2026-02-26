export type Period = "hour" | "day" | "week" | "month";

export type MetricValue = {
  name: string;
  value: number;
  timestamp: number;
  tags: string;
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

export type MetricId = string;

export type MetricData = {
  name: string;
  value: number;
  timestamp: number;
  tags: string;
};

export type AggregatedMetricId = string;

export type AggregatedMetricData = {
  metricName: string;
  period: Period;
  periodStart: number;
  count: number;
  sum: number;
  min: number;
  max: number;
  avg: number;
};

export type ReportId = string;

export type ReportData = {
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
