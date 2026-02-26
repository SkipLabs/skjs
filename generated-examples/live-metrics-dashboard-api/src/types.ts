export type MetricId = string;

export type MetricValue = {
  name: string;
  value: number;
  unit: string;
  timestamp: number;
  tags: string | null;
};

export type Metric = MetricValue & { id: MetricId };
