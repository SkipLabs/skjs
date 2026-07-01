import type { Json } from "@skipruntime/core";

export type AggregateBucket = {
  readonly avg: number;
  readonly bucketStart: string;
  readonly count: number;
  readonly max: number;
  readonly min: number;
  readonly sum: number;
} & { readonly [key: string]: Json | null };

export type AggregateBucket_skip_id_ = {
  readonly avg: number;
  readonly bucketStart: string;
  readonly count: number;
  readonly max: number;
  readonly min: number;
  readonly sum: number;
} & { readonly [key: string]: Json | null };

export type AggregateBucket_skip_value_ = {
  readonly avg: number;
  readonly bucketStart: string;
  readonly count: number;
  readonly max: number;
  readonly min: number;
  readonly sum: number;
} & { readonly [key: string]: Json | null };

export type AggregateResponse = {
  readonly buckets: AggregateBucket[];
  readonly name: string;
  readonly period: Period;
  readonly since: string;
  readonly until: string;
} & { readonly [key: string]: Json | null };

export type AggregateResponse_skip_id_ = {
  readonly buckets: AggregateBucket[];
  readonly name: string;
  readonly period: Period;
  readonly since: string;
  readonly until: string;
} & { readonly [key: string]: Json | null };

export type AggregateResponse_skip_value_ = {
  readonly buckets: AggregateBucket[];
  readonly name: string;
  readonly period: Period;
  readonly since: string;
  readonly until: string;
} & { readonly [key: string]: Json | null };

export type ApiError = { readonly code: string; readonly message: string } & {
  readonly [key: string]: Json | null;
};

export type ApiError_skip_id_ = {
  readonly code: string;
  readonly message: string;
} & { readonly [key: string]: Json | null };

export type ApiError_skip_value_ = {
  readonly code: string;
  readonly message: string;
} & { readonly [key: string]: Json | null };

export type CreateMetricRequest = {
  readonly name: string;
  readonly occurredAt: string;
  readonly tags?: CreateMetricRequestTags;
  readonly value: number;
} & { readonly [key: string]: Json | null };

export type CreateMetricRequestTags = Record<string, string>;

export type CreateMetricRequestTags_skip_id_ = Record<string, string>;

export type CreateMetricRequestTags_skip_value_ = Record<string, string>;

export type CreateMetricRequest_skip_id_ = {
  readonly name: string;
  readonly occurredAt: string;
  readonly tags?: CreateMetricRequestTags;
  readonly value: number;
} & { readonly [key: string]: Json | null };

export type CreateMetricRequest_skip_value_ = {
  readonly name: string;
  readonly occurredAt: string;
  readonly tags?: CreateMetricRequestTags;
  readonly value: number;
} & { readonly [key: string]: Json | null };

export type GetMetricParams = {
  readonly metricId: string;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type ListMetricsParams = { readonly userId: string } & {
  readonly [key: string]: Json | null;
};

export type Metric = {
  readonly createdAt: string;
  readonly id: string;
  readonly name: string;
  readonly occurredAt: string;
  readonly ownerId: string;
  readonly tags?: MetricTags;
  readonly value: number;
} & { readonly [key: string]: Json | null };

export type MetricPage = {
  readonly items: Metric[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type MetricPage_skip_id_ = {
  readonly items: Metric[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type MetricPage_skip_value_ = {
  readonly items: Metric[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type MetricTags = Record<string, string>;

export type MetricTags_skip_id_ = Record<string, string>;

export type MetricTags_skip_value_ = Record<string, string>;

export type Metric_skip_id_ = string;

export type Metric_skip_value_ = {
  readonly createdAt: string;
  readonly name: string;
  readonly occurredAt: string;
  readonly ownerId: string;
  readonly tags?: MetricTags;
  readonly value: number;
} & { readonly [key: string]: Json | null };

export type Period = "hour" | "day" | "week" | "month";

export type Period_skip_id_ = "hour" | "day" | "week" | "month";

export type Period_skip_value_ = "hour" | "day" | "week" | "month";

export type SummaryStat = {
  readonly avg: number;
  readonly count: number;
  readonly max?: number;
  readonly min?: number;
  readonly name: string;
  readonly sum: number;
} & { readonly [key: string]: Json | null };

export type SummaryStat_skip_id_ = {
  readonly avg: number;
  readonly count: number;
  readonly max?: number;
  readonly min?: number;
  readonly name: string;
  readonly sum: number;
} & { readonly [key: string]: Json | null };

export type SummaryStat_skip_value_ = {
  readonly avg: number;
  readonly count: number;
  readonly max?: number;
  readonly min?: number;
  readonly name: string;
  readonly sum: number;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest = {
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest_skip_id_ = {
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest_skip_value_ = {
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };

export type User = {
  readonly displayName?: string;
  readonly email?: string;
  readonly id: string;
} & { readonly [key: string]: Json | null };

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };
