export type AggregationPeriod = "HOUR" | "DAY" | "WEEK" | "MONTH";

export type AggregationPeriod_skip_id_ = "HOUR" | "DAY" | "WEEK" | "MONTH";

export type AggregationPeriod_skip_value_ = "HOUR" | "DAY" | "WEEK" | "MONTH";

export type ApiError = { readonly code: string; readonly message: string };

export type ApiError_skip_id_ = {
  readonly code: string;
  readonly message: string;
};

export type ApiError_skip_value_ = {
  readonly code: string;
  readonly message: string;
};

export type CreateDashboardRequest = {
  readonly description?: string;
  readonly name: string;
  readonly panels?: DashboardPanel[];
};

export type CreateDashboardRequest_skip_id_ = {
  readonly description?: string;
  readonly name: string;
  readonly panels?: DashboardPanel[];
};

export type CreateDashboardRequest_skip_value_ = {
  readonly description?: string;
  readonly name: string;
  readonly panels?: DashboardPanel[];
};

export type CreateMetricRequest = {
  readonly description?: string;
  readonly displayName?: string;
  readonly kind: MetricKind;
  readonly name: string;
  readonly unit?: string;
};

export type CreateMetricRequest_skip_id_ = {
  readonly description?: string;
  readonly displayName?: string;
  readonly kind: MetricKind;
  readonly name: string;
  readonly unit?: string;
};

export type CreateMetricRequest_skip_value_ = {
  readonly description?: string;
  readonly displayName?: string;
  readonly kind: MetricKind;
  readonly name: string;
  readonly unit?: string;
};

export type Dashboard = {
  readonly createdAt: string;
  readonly description?: string;
  readonly id: string;
  readonly name: string;
  readonly ownerId: string;
  readonly panels: DashboardPanel[];
  readonly updatedAt?: string;
};

export type DashboardList = {
  readonly items: Dashboard[];
  readonly limit: number;
  readonly offset: number;
};

export type DashboardList_skip_id_ = {
  readonly items: Dashboard[];
  readonly limit: number;
  readonly offset: number;
};

export type DashboardList_skip_value_ = {
  readonly items: Dashboard[];
  readonly limit: number;
  readonly offset: number;
};

export type DashboardPanel = {
  readonly metricId: string;
  readonly period: AggregationPeriod;
  readonly title?: string;
};

export type DashboardPanel_skip_id_ = {
  readonly metricId: string;
  readonly period: AggregationPeriod;
  readonly title?: string;
};

export type DashboardPanel_skip_value_ = {
  readonly metricId: string;
  readonly period: AggregationPeriod;
  readonly title?: string;
};

export type Dashboard_skip_id_ = string;

export type Dashboard_skip_value_ = {
  readonly createdAt: string;
  readonly description?: string;
  readonly name: string;
  readonly ownerId: string;
  readonly panels: DashboardPanel[];
  readonly updatedAt?: string;
};

export type IngestMetricEventRequest = {
  readonly occurredAt?: string;
  readonly tags?: IngestMetricEventRequestTags;
  readonly value?: number;
};

export type IngestMetricEventRequestTags = Record<string, string>;

export type IngestMetricEventRequestTags_skip_id_ = Record<string, string>;

export type IngestMetricEventRequestTags_skip_value_ = Record<string, string>;

export type IngestMetricEventRequest_skip_id_ = {
  readonly occurredAt?: string;
  readonly tags?: IngestMetricEventRequestTags;
  readonly value?: number;
};

export type IngestMetricEventRequest_skip_value_ = {
  readonly occurredAt?: string;
  readonly tags?: IngestMetricEventRequestTags;
  readonly value?: number;
};

export type Metric = {
  readonly createdAt: string;
  readonly description?: string;
  readonly displayName?: string;
  readonly id: string;
  readonly kind: MetricKind;
  readonly name: string;
  readonly ownerId: string;
  readonly unit?: string;
  readonly updatedAt?: string;
};

export type MetricEvent = {
  readonly createdAt: string;
  readonly id: string;
  readonly metricId: string;
  readonly occurredAt: string;
  readonly ownerId: string;
  readonly tags?: MetricEventTags;
  readonly value: number;
};

export type MetricEventKey = { readonly id: string; readonly metricId: string };

export type MetricEventList = {
  readonly items: MetricEvent[];
  readonly limit: number;
  readonly offset: number;
};

export type MetricEventList_skip_id_ = {
  readonly items: MetricEvent[];
  readonly limit: number;
  readonly offset: number;
};

export type MetricEventList_skip_value_ = {
  readonly items: MetricEvent[];
  readonly limit: number;
  readonly offset: number;
};

export type MetricEventTags = Record<string, string>;

export type MetricEventTags_skip_id_ = Record<string, string>;

export type MetricEventTags_skip_value_ = Record<string, string>;

export type MetricEvent_skip_id_ = {
  readonly id: string;
  readonly metricId: string;
};

export type MetricEvent_skip_value_ = {
  readonly createdAt: string;
  readonly occurredAt: string;
  readonly ownerId: string;
  readonly tags?: MetricEventTags;
  readonly value: number;
};

export type MetricKind = "COUNTER" | "GAUGE" | "HISTOGRAM";

export type MetricKind_skip_id_ = "COUNTER" | "GAUGE" | "HISTOGRAM";

export type MetricKind_skip_value_ = "COUNTER" | "GAUGE" | "HISTOGRAM";

export type MetricList = {
  readonly items: Metric[];
  readonly limit: number;
  readonly offset: number;
};

export type MetricList_skip_id_ = {
  readonly items: Metric[];
  readonly limit: number;
  readonly offset: number;
};

export type MetricList_skip_value_ = {
  readonly items: Metric[];
  readonly limit: number;
  readonly offset: number;
};

export type MetricStatBucket = {
  readonly avg: number;
  readonly bucketEnd: string;
  readonly bucketStart: string;
  readonly count: number;
  readonly max: number;
  readonly min: number;
  readonly sum: number;
};

export type MetricStatBucket_skip_id_ = {
  readonly avg: number;
  readonly bucketEnd: string;
  readonly bucketStart: string;
  readonly count: number;
  readonly max: number;
  readonly min: number;
  readonly sum: number;
};

export type MetricStatBucket_skip_value_ = {
  readonly avg: number;
  readonly bucketEnd: string;
  readonly bucketStart: string;
  readonly count: number;
  readonly max: number;
  readonly min: number;
  readonly sum: number;
};

export type MetricStats = {
  readonly buckets: MetricStatBucket[];
  readonly metricId: string;
  readonly period: AggregationPeriod;
  readonly since?: string;
  readonly until?: string;
};

export type MetricStats_skip_id_ = {
  readonly buckets: MetricStatBucket[];
  readonly metricId: string;
  readonly period: AggregationPeriod;
  readonly since?: string;
  readonly until?: string;
};

export type MetricStats_skip_value_ = {
  readonly buckets: MetricStatBucket[];
  readonly metricId: string;
  readonly period: AggregationPeriod;
  readonly since?: string;
  readonly until?: string;
};

export type Metric_skip_id_ = string;

export type Metric_skip_value_ = {
  readonly createdAt: string;
  readonly description?: string;
  readonly displayName?: string;
  readonly kind: MetricKind;
  readonly name: string;
  readonly ownerId: string;
  readonly unit?: string;
  readonly updatedAt?: string;
};

export type UpdateDashboardRequest = {
  readonly description?: string;
  readonly name?: string;
  readonly panels?: DashboardPanel[];
};

export type UpdateDashboardRequest_skip_id_ = {
  readonly description?: string;
  readonly name?: string;
  readonly panels?: DashboardPanel[];
};

export type UpdateDashboardRequest_skip_value_ = {
  readonly description?: string;
  readonly name?: string;
  readonly panels?: DashboardPanel[];
};

export type UpdateMeRequest = {
  readonly avatarUrl?: string;
  readonly displayName?: string;
  readonly email?: string;
};

export type UpdateMeRequest_skip_id_ = {
  readonly avatarUrl?: string;
  readonly displayName?: string;
  readonly email?: string;
};

export type UpdateMeRequest_skip_value_ = {
  readonly avatarUrl?: string;
  readonly displayName?: string;
  readonly email?: string;
};

export type UpdateMetricRequest = {
  readonly description?: string;
  readonly displayName?: string;
  readonly unit?: string;
};

export type UpdateMetricRequest_skip_id_ = {
  readonly description?: string;
  readonly displayName?: string;
  readonly unit?: string;
};

export type UpdateMetricRequest_skip_value_ = {
  readonly description?: string;
  readonly displayName?: string;
  readonly unit?: string;
};

export type User = {
  readonly avatarUrl?: string;
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly id: string;
  readonly updatedAt?: string;
};

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly avatarUrl?: string;
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly updatedAt?: string;
};
