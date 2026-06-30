export type ApiError = { readonly code: string; readonly message: string };

export type ApiError_skip_id_ = {
  readonly code: string;
  readonly message: string;
};

export type ApiError_skip_value_ = {
  readonly code: string;
  readonly message: string;
};

export type Component = {
  readonly createdAt: string;
  readonly criticality: Criticality;
  readonly description?: string;
  readonly displayName?: string;
  readonly id: string;
  readonly lastHeartbeatAt?: string;
  readonly lastMessage?: string;
  readonly name: string;
  readonly registeredByUserId: string;
  readonly status: ComponentStatus;
};

export type ComponentIdKey = string;

export type ComponentList = {
  readonly items: Component[];
  readonly total?: number;
};

export type ComponentList_skip_id_ = {
  readonly items: Component[];
  readonly total?: number;
};

export type ComponentList_skip_value_ = {
  readonly items: Component[];
  readonly total?: number;
};

export type ComponentStatus = "HEALTHY" | "DEGRADED" | "UNHEALTHY" | "UNKNOWN";

export type ComponentStatus_skip_id_ =
  | "HEALTHY"
  | "DEGRADED"
  | "UNHEALTHY"
  | "UNKNOWN";

export type ComponentStatus_skip_value_ =
  | "HEALTHY"
  | "DEGRADED"
  | "UNHEALTHY"
  | "UNKNOWN";

export type ComponentStored = {
  readonly createdAt: string;
  readonly criticality: Criticality;
  readonly description?: string;
  readonly displayName?: string;
  readonly lastHeartbeatAt?: string;
  readonly lastMessage?: string;
  readonly name: string;
  readonly registeredByUserId: string;
  readonly status: ComponentStatus;
};

export type Component_skip_id_ = string;

export type Component_skip_value_ = {
  readonly createdAt: string;
  readonly criticality: Criticality;
  readonly description?: string;
  readonly displayName?: string;
  readonly lastHeartbeatAt?: string;
  readonly lastMessage?: string;
  readonly name: string;
  readonly registeredByUserId: string;
  readonly status: ComponentStatus;
};

export type Criticality = "CRITICAL" | "STANDARD" | "INFORMATIONAL";

export type Criticality_skip_id_ = "CRITICAL" | "STANDARD" | "INFORMATIONAL";

export type Criticality_skip_value_ = "CRITICAL" | "STANDARD" | "INFORMATIONAL";

export type GetComponentParams = { readonly componentId: string };

export type GetMeParams = { readonly userId: string };

export type Heartbeat = {
  readonly componentId: string;
  readonly id: string;
  readonly message?: string;
  readonly receivedAt: string;
  readonly reportedByUserId: string;
  readonly status: ComponentStatus;
};

export type HeartbeatList = {
  readonly items: Heartbeat[];
  readonly total?: number;
};

export type HeartbeatList_skip_id_ = {
  readonly items: Heartbeat[];
  readonly total?: number;
};

export type HeartbeatList_skip_value_ = {
  readonly items: Heartbeat[];
  readonly total?: number;
};

export type Heartbeat_skip_id_ = string;

export type Heartbeat_skip_value_ = {
  readonly componentId: string;
  readonly message?: string;
  readonly receivedAt: string;
  readonly reportedByUserId: string;
  readonly status: ComponentStatus;
};

export type ListComponentsParams = { readonly status?: ComponentStatus };

export type ListHeartbeatsParams = { readonly componentId: string };

export type RegisterComponentRequest = {
  readonly criticality: Criticality;
  readonly description?: string;
  readonly displayName?: string;
  readonly name: string;
};

export type RegisterComponentRequest_skip_id_ = {
  readonly criticality: Criticality;
  readonly description?: string;
  readonly displayName?: string;
  readonly name: string;
};

export type RegisterComponentRequest_skip_value_ = {
  readonly criticality: Criticality;
  readonly description?: string;
  readonly displayName?: string;
  readonly name: string;
};

export type StatusCounts = {
  readonly DEGRADED: number;
  readonly HEALTHY: number;
  readonly UNHEALTHY: number;
  readonly UNKNOWN: number;
};

export type StatusCounts_skip_id_ = {
  readonly DEGRADED: number;
  readonly HEALTHY: number;
  readonly UNHEALTHY: number;
  readonly UNKNOWN: number;
};

export type StatusCounts_skip_value_ = {
  readonly DEGRADED: number;
  readonly HEALTHY: number;
  readonly UNHEALTHY: number;
  readonly UNKNOWN: number;
};

export type SubmitHeartbeatRequest = {
  readonly message?: string;
  readonly status: ComponentStatus;
};

export type SubmitHeartbeatRequest_skip_id_ = {
  readonly message?: string;
  readonly status: ComponentStatus;
};

export type SubmitHeartbeatRequest_skip_value_ = {
  readonly message?: string;
  readonly status: ComponentStatus;
};

export type SystemHealth = {
  readonly componentCount: number;
  readonly computedAt: string;
  readonly criticalUnhealthyCount: number;
  readonly overallStatus: ComponentStatus;
  readonly statusCounts: StatusCounts;
};

export type SystemHealthAggregate = {
  readonly componentCount: number;
  readonly criticalUnhealthyCount: number;
  readonly degradedCount: number;
  readonly healthyCount: number;
  readonly unhealthyCount: number;
  readonly unknownCount: number;
};

export type SystemHealth_skip_id_ = {
  readonly componentCount: number;
  readonly computedAt: string;
  readonly criticalUnhealthyCount: number;
  readonly overallStatus: ComponentStatus;
  readonly statusCounts: StatusCounts;
};

export type SystemHealth_skip_value_ = {
  readonly componentCount: number;
  readonly computedAt: string;
  readonly criticalUnhealthyCount: number;
  readonly overallStatus: ComponentStatus;
  readonly statusCounts: StatusCounts;
};

export type UpdateComponentRequest = {
  readonly criticality?: Criticality;
  readonly description?: string;
  readonly displayName?: string;
};

export type UpdateComponentRequest_skip_id_ = {
  readonly criticality?: Criticality;
  readonly description?: string;
  readonly displayName?: string;
};

export type UpdateComponentRequest_skip_value_ = {
  readonly criticality?: Criticality;
  readonly description?: string;
  readonly displayName?: string;
};

export type UpdateMeRequest = {
  readonly displayName?: string;
  readonly email?: string;
};

export type UpdateMeRequest_skip_id_ = {
  readonly displayName?: string;
  readonly email?: string;
};

export type UpdateMeRequest_skip_value_ = {
  readonly displayName?: string;
  readonly email?: string;
};

export type User = {
  readonly displayName?: string;
  readonly email?: string;
  readonly id: string;
};

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly displayName?: string;
  readonly email?: string;
};
