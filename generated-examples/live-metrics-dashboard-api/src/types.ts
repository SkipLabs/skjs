export type MetricId = string;

export type MetricValue = {
  name: string;
  value: number;
  unit: string;
  timestamp: number;
  tags: { [name: string]: string } | null;
};

export type Metric = MetricValue & { id: MetricId };
