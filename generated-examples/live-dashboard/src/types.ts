import type { Json } from "@skipruntime/core";

export type ApiError = { readonly code?: string; readonly message: string } & {
  readonly [key: string]: Json | null;
};

export type ApiError_skip_id_ = {
  readonly code?: string;
  readonly message: string;
} & { readonly [key: string]: Json | null };

export type ApiError_skip_value_ = {
  readonly code?: string;
  readonly message: string;
} & { readonly [key: string]: Json | null };

export type ChartType = "line" | "bar" | "gauge" | "number" | "area";

export type ChartType_skip_id_ = "line" | "bar" | "gauge" | "number" | "area";

export type ChartType_skip_value_ =
  | "line"
  | "bar"
  | "gauge"
  | "number"
  | "area";

export type CreateDashboardRequest = {
  readonly description?: string;
  readonly name: string;
} & { readonly [key: string]: Json | null };

export type CreateDashboardRequest_skip_id_ = {
  readonly description?: string;
  readonly name: string;
} & { readonly [key: string]: Json | null };

export type CreateDashboardRequest_skip_value_ = {
  readonly description?: string;
  readonly name: string;
} & { readonly [key: string]: Json | null };

export type CreateMetricRequest = {
  readonly description?: string;
  readonly kind: MetricKind;
  readonly name: string;
  readonly unit?: string;
} & { readonly [key: string]: Json | null };

export type CreateMetricRequest_skip_id_ = {
  readonly description?: string;
  readonly kind: MetricKind;
  readonly name: string;
  readonly unit?: string;
} & { readonly [key: string]: Json | null };

export type CreateMetricRequest_skip_value_ = {
  readonly description?: string;
  readonly kind: MetricKind;
  readonly name: string;
  readonly unit?: string;
} & { readonly [key: string]: Json | null };

export type CreateWidgetRequest = {
  readonly chartType: ChartType;
  readonly height: number;
  readonly metricId: string;
  readonly positionX: number;
  readonly positionY: number;
  readonly title: string;
  readonly width: number;
} & { readonly [key: string]: Json | null };

export type CreateWidgetRequest_skip_id_ = {
  readonly chartType: ChartType;
  readonly height: number;
  readonly metricId: string;
  readonly positionX: number;
  readonly positionY: number;
  readonly title: string;
  readonly width: number;
} & { readonly [key: string]: Json | null };

export type CreateWidgetRequest_skip_value_ = {
  readonly chartType: ChartType;
  readonly height: number;
  readonly metricId: string;
  readonly positionX: number;
  readonly positionY: number;
  readonly title: string;
  readonly width: number;
} & { readonly [key: string]: Json | null };

export type Dashboard = {
  readonly createdAt: string;
  readonly description?: string;
  readonly id: string;
  readonly name: string;
  readonly ownerId: string;
  readonly updatedAt: string;
  readonly widgetCount?: number;
  readonly widgets?: Widget[];
} & { readonly [key: string]: Json | null };

export type DashboardList = { readonly items: Dashboard[] } & {
  readonly [key: string]: Json | null;
};

export type DashboardList_skip_id_ = { readonly items: Dashboard[] } & {
  readonly [key: string]: Json | null;
};

export type DashboardList_skip_value_ = { readonly items: Dashboard[] } & {
  readonly [key: string]: Json | null;
};

export type DashboardStored = {
  readonly createdAt: string;
  readonly description?: string;
  readonly id: string;
  readonly name: string;
  readonly ownerId: string;
  readonly updatedAt: string;
} & { readonly [key: string]: Json | null };

export type DashboardStreamEvent = {
  readonly dashboardId: string;
  readonly metricId: string;
  readonly point: MetricPoint;
  readonly widgetId: string;
} & { readonly [key: string]: Json | null };

export type DashboardStreamEvent_skip_id_ = {
  readonly dashboardId: string;
  readonly metricId: string;
  readonly point: MetricPoint;
  readonly widgetId: string;
} & { readonly [key: string]: Json | null };

export type DashboardStreamEvent_skip_value_ = {
  readonly dashboardId: string;
  readonly metricId: string;
  readonly point: MetricPoint;
  readonly widgetId: string;
} & { readonly [key: string]: Json | null };

export type Dashboard_skip_id_ = string;

export type Dashboard_skip_value_ = {
  readonly createdAt: string;
  readonly description?: string;
  readonly name: string;
  readonly ownerId: string;
  readonly updatedAt: string;
  readonly widgetCount?: number;
  readonly widgets?: Widget[];
} & { readonly [key: string]: Json | null };

export type GetDashboardParams = {
  readonly dashboardId: string;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type GetMetricParams = {
  readonly metricId: string;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type GetWidgetParams = { readonly widgetId: string } & {
  readonly [key: string]: Json | null;
};

export type IngestMetricPointRequest = {
  readonly labels?: IngestMetricPointRequestLabels;
  readonly timestamp?: string;
  readonly value: number;
} & { readonly [key: string]: Json | null };

export type IngestMetricPointRequestLabels = Record<string, string>;

export type IngestMetricPointRequestLabels_skip_id_ = Record<string, string>;

export type IngestMetricPointRequestLabels_skip_value_ = Record<string, string>;

export type IngestMetricPointRequest_skip_id_ = {
  readonly labels?: IngestMetricPointRequestLabels;
  readonly timestamp?: string;
  readonly value: number;
} & { readonly [key: string]: Json | null };

export type IngestMetricPointRequest_skip_value_ = {
  readonly labels?: IngestMetricPointRequestLabels;
  readonly timestamp?: string;
  readonly value: number;
} & { readonly [key: string]: Json | null };

export type ListDashboardsParams = { readonly userId: string } & {
  readonly [key: string]: Json | null;
};

export type ListMetricPointsParams = { readonly metricId: string } & {
  readonly [key: string]: Json | null;
};

export type ListMetricsParams = { readonly userId: string } & {
  readonly [key: string]: Json | null;
};

export type ListWidgetsParams = { readonly dashboardId: string } & {
  readonly [key: string]: Json | null;
};

export type Metric = {
  readonly avgValue?: number;
  readonly createdAt: string;
  readonly description?: string;
  readonly id: string;
  readonly kind: MetricKind;
  readonly lastTimestamp?: string;
  readonly lastValue?: number;
  readonly maxValue?: number;
  readonly minValue?: number;
  readonly name: string;
  readonly ownerId: string;
  readonly pointCount?: number;
  readonly unit?: string;
  readonly updatedAt: string;
} & { readonly [key: string]: Json | null };

export type MetricKind = "gauge" | "counter" | "rate";

export type MetricKind_skip_id_ = "gauge" | "counter" | "rate";

export type MetricKind_skip_value_ = "gauge" | "counter" | "rate";

export type MetricList = { readonly items: Metric[] } & {
  readonly [key: string]: Json | null;
};

export type MetricList_skip_id_ = { readonly items: Metric[] } & {
  readonly [key: string]: Json | null;
};

export type MetricList_skip_value_ = { readonly items: Metric[] } & {
  readonly [key: string]: Json | null;
};

export type MetricPoint = {
  readonly labels?: MetricPointLabels;
  readonly metricId: string;
  readonly timestamp: string;
  readonly value: number;
} & { readonly [key: string]: Json | null };

export type MetricPointCompositeKey = {
  readonly metricId: string;
  readonly timestamp: string;
} & { readonly [key: string]: Json | null };

export type MetricPointLabels = Record<string, string>;

export type MetricPointLabels_skip_id_ = Record<string, string>;

export type MetricPointLabels_skip_value_ = Record<string, string>;

export type MetricPointList = { readonly items: MetricPoint[] } & {
  readonly [key: string]: Json | null;
};

export type MetricPointList_skip_id_ = { readonly items: MetricPoint[] } & {
  readonly [key: string]: Json | null;
};

export type MetricPointList_skip_value_ = { readonly items: MetricPoint[] } & {
  readonly [key: string]: Json | null;
};

export type MetricPointValue = {
  readonly labels?: MetricPointLabels;
  readonly value: number;
} & { readonly [key: string]: Json | null };

export type MetricPoint_skip_id_ = {
  readonly metricId: string;
  readonly timestamp: string;
} & { readonly [key: string]: Json | null };

export type MetricPoint_skip_value_ = {
  readonly labels?: MetricPointLabels;
  readonly value: number;
} & { readonly [key: string]: Json | null };

export type MetricStats = {
  readonly avgValue?: number;
  readonly lastTimestamp?: string;
  readonly lastValue?: number;
  readonly maxValue?: number;
  readonly minValue?: number;
  readonly pointCount: number;
} & { readonly [key: string]: Json | null };

export type MetricStored = {
  readonly createdAt: string;
  readonly description?: string;
  readonly id: string;
  readonly kind: MetricKind;
  readonly name: string;
  readonly ownerId: string;
  readonly unit?: string;
  readonly updatedAt: string;
} & { readonly [key: string]: Json | null };

export type MetricStreamEvent = {
  readonly metricId: string;
  readonly point: MetricPoint;
} & { readonly [key: string]: Json | null };

export type MetricStreamEvent_skip_id_ = {
  readonly metricId: string;
  readonly point: MetricPoint;
} & { readonly [key: string]: Json | null };

export type MetricStreamEvent_skip_value_ = {
  readonly metricId: string;
  readonly point: MetricPoint;
} & { readonly [key: string]: Json | null };

export type Metric_skip_id_ = string;

export type Metric_skip_value_ = {
  readonly avgValue?: number;
  readonly createdAt: string;
  readonly description?: string;
  readonly kind: MetricKind;
  readonly lastTimestamp?: string;
  readonly lastValue?: number;
  readonly maxValue?: number;
  readonly minValue?: number;
  readonly name: string;
  readonly ownerId: string;
  readonly pointCount?: number;
  readonly unit?: string;
  readonly updatedAt: string;
} & { readonly [key: string]: Json | null };

export type UpdateDashboardRequest = {
  readonly description?: string;
  readonly name?: string;
} & { readonly [key: string]: Json | null };

export type UpdateDashboardRequest_skip_id_ = {
  readonly description?: string;
  readonly name?: string;
} & { readonly [key: string]: Json | null };

export type UpdateDashboardRequest_skip_value_ = {
  readonly description?: string;
  readonly name?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest = {
  readonly avatarUrl?: string;
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest_skip_id_ = {
  readonly avatarUrl?: string;
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest_skip_value_ = {
  readonly avatarUrl?: string;
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMetricRequest = {
  readonly description?: string;
  readonly name?: string;
  readonly unit?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMetricRequest_skip_id_ = {
  readonly description?: string;
  readonly name?: string;
  readonly unit?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMetricRequest_skip_value_ = {
  readonly description?: string;
  readonly name?: string;
  readonly unit?: string;
} & { readonly [key: string]: Json | null };

export type UpdateWidgetRequest = {
  readonly chartType?: ChartType;
  readonly height?: number;
  readonly positionX?: number;
  readonly positionY?: number;
  readonly title?: string;
  readonly width?: number;
} & { readonly [key: string]: Json | null };

export type UpdateWidgetRequest_skip_id_ = {
  readonly chartType?: ChartType;
  readonly height?: number;
  readonly positionX?: number;
  readonly positionY?: number;
  readonly title?: string;
  readonly width?: number;
} & { readonly [key: string]: Json | null };

export type UpdateWidgetRequest_skip_value_ = {
  readonly chartType?: ChartType;
  readonly height?: number;
  readonly positionX?: number;
  readonly positionY?: number;
  readonly title?: string;
  readonly width?: number;
} & { readonly [key: string]: Json | null };

export type User = {
  readonly avatarUrl?: string;
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly id: string;
  readonly updatedAt?: string;
} & { readonly [key: string]: Json | null };

export type UserStored = {
  readonly avatarUrl?: string;
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly id: string;
  readonly updatedAt?: string;
} & { readonly [key: string]: Json | null };

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly avatarUrl?: string;
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly updatedAt?: string;
} & { readonly [key: string]: Json | null };

export type Widget = {
  readonly chartType: ChartType;
  readonly createdAt: string;
  readonly dashboardId: string;
  readonly height: number;
  readonly id: string;
  readonly metricId: string;
  readonly positionX: number;
  readonly positionY: number;
  readonly title: string;
  readonly updatedAt: string;
  readonly width: number;
} & { readonly [key: string]: Json | null };

export type WidgetList = { readonly items: Widget[] } & {
  readonly [key: string]: Json | null;
};

export type WidgetList_skip_id_ = { readonly items: Widget[] } & {
  readonly [key: string]: Json | null;
};

export type WidgetList_skip_value_ = { readonly items: Widget[] } & {
  readonly [key: string]: Json | null;
};

export type Widget_skip_id_ = string;

export type Widget_skip_value_ = {
  readonly chartType: ChartType;
  readonly createdAt: string;
  readonly dashboardId: string;
  readonly height: number;
  readonly metricId: string;
  readonly positionX: number;
  readonly positionY: number;
  readonly title: string;
  readonly updatedAt: string;
  readonly width: number;
} & { readonly [key: string]: Json | null };
