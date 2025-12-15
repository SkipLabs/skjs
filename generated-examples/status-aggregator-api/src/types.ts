export type HealthyDegradedUnhealthyEnum = "healthy" | "degraded" | "unhealthy";

export type ComponentId = string;

export type ComponentValue = {
  name: string;
  status: HealthyDegradedUnhealthyEnum;
  lastChecked: number;
  message: string | null;
};

export type Component = ComponentValue & { id: ComponentId };

export type SystemStatusId = string;

export type SystemStatusValue = {
  overallStatus: HealthyDegradedUnhealthyEnum;
  componentCount: number;
  healthyCount: number;
  degradedCount: number;
  unhealthyCount: number;
  lastUpdated: number;
};

export type SystemStatus = SystemStatusValue & { id: SystemStatusId };
