import type { Json } from "@skipruntime/core";

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

export type Component = {
  readonly createdAt: string;
  readonly description?: string;
  readonly id: string;
  readonly lastReportedAt: string;
  readonly name: string;
  readonly status: ComponentStatus;
} & { readonly [key: string]: Json | null };

export type ComponentList = { readonly components: Component[] } & {
  readonly [key: string]: Json | null;
};

export type ComponentList_skip_id_ = { readonly components: Component[] } & {
  readonly [key: string]: Json | null;
};

export type ComponentList_skip_value_ = { readonly components: Component[] } & {
  readonly [key: string]: Json | null;
};

export type ComponentStatus = "HEALTHY" | "DEGRADED" | "UNHEALTHY";

export type ComponentStatusCount = number;

export type ComponentStatusKey = string;

export type ComponentStatus_skip_id_ = "HEALTHY" | "DEGRADED" | "UNHEALTHY";

export type ComponentStatus_skip_value_ = "HEALTHY" | "DEGRADED" | "UNHEALTHY";

export type Component_skip_id_ = string;

export type Component_skip_value_ = {
  readonly createdAt: string;
  readonly description?: string;
  readonly lastReportedAt: string;
  readonly name: string;
  readonly status: ComponentStatus;
} & { readonly [key: string]: Json | null };

export type GetComponentParams = { readonly componentId: string } & {
  readonly [key: string]: Json | null;
};

export type ListComponentsParams = { readonly status?: ComponentStatus } & {
  readonly [key: string]: Json | null;
};

export type RegisterComponentRequest = {
  readonly description?: string;
  readonly name: string;
  readonly status: ComponentStatus;
} & { readonly [key: string]: Json | null };

export type RegisterComponentRequest_skip_id_ = {
  readonly description?: string;
  readonly name: string;
  readonly status: ComponentStatus;
} & { readonly [key: string]: Json | null };

export type RegisterComponentRequest_skip_value_ = {
  readonly description?: string;
  readonly name: string;
  readonly status: ComponentStatus;
} & { readonly [key: string]: Json | null };

export type ReportComponentStatusRequest = {
  readonly status: ComponentStatus;
} & { readonly [key: string]: Json | null };

export type ReportComponentStatusRequest_skip_id_ = {
  readonly status: ComponentStatus;
} & { readonly [key: string]: Json | null };

export type ReportComponentStatusRequest_skip_value_ = {
  readonly status: ComponentStatus;
} & { readonly [key: string]: Json | null };

export type SystemHealth = {
  readonly checkedAt: string;
  readonly degradedCount: number;
  readonly healthyCount: number;
  readonly status: SystemStatus;
  readonly totalCount: number;
  readonly unhealthyCount: number;
} & { readonly [key: string]: Json | null };

export type SystemHealthStored = { readonly status: SystemStatus } & {
  readonly [key: string]: Json | null;
};

export type SystemHealth_skip_id_ = {
  readonly checkedAt: string;
  readonly degradedCount: number;
  readonly healthyCount: number;
  readonly status: SystemStatus;
  readonly totalCount: number;
  readonly unhealthyCount: number;
} & { readonly [key: string]: Json | null };

export type SystemHealth_skip_value_ = {
  readonly checkedAt: string;
  readonly degradedCount: number;
  readonly healthyCount: number;
  readonly status: SystemStatus;
  readonly totalCount: number;
  readonly unhealthyCount: number;
} & { readonly [key: string]: Json | null };

export type SystemStatus = "HEALTHY" | "DEGRADED" | "UNHEALTHY";

export type SystemStatus_skip_id_ = "HEALTHY" | "DEGRADED" | "UNHEALTHY";

export type SystemStatus_skip_value_ = "HEALTHY" | "DEGRADED" | "UNHEALTHY";

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
