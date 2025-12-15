import type {
  EagerCollection,
  Entry,
  Json,
  Resource,
  SkipService,
  Context,
  Mapper,
  Values
} from "@skipruntime/core";

import type {
  MetricId,
  MetricValue,
} from "./types.js";


type Inputs = {
  metrics: Entry<MetricId, MetricValue>[];
};

export type InputCollections = {
  metrics: EagerCollection<MetricId, MetricValue>;
};

export type OrderedMetricKey = [number, MetricId];

export type GraphCollections = {
  metrics: EagerCollection<OrderedMetricKey, MetricValue>;
};

type Resources = {
  "metrics": new (params: Json) => Resource<GraphCollections>;
};

class OrderByTimestampMapper implements Mapper<MetricId, MetricValue, OrderedMetricKey, MetricValue> {
  mapEntry(
    key: MetricId,
    values: Values<MetricValue>,
    _context: Context
  ): Iterable<[OrderedMetricKey, MetricValue]> {
    const arr = values.toArray();
    const result: Array<[OrderedMetricKey, MetricValue]> = Array.of();
    for (let i = 0; i < arr.length; i++) {
      const v = arr[i]!;
      const orderedKey: OrderedMetricKey = [v.timestamp, key];
      result.push([orderedKey, v]);
    }
    return result;
  }
}

export class MetricsResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<OrderedMetricKey, MetricValue> {
    return cs.metrics;
  }
}

class Service implements SkipService<InputCollections, GraphCollections> {
  public initialData: Inputs;
  public resources: Resources;

  constructor() {
    const emptyMetrics: Entry<MetricId, MetricValue>[] = Array.of();
    this.initialData = { metrics: emptyMetrics };
    this.resources = { "metrics": MetricsResource };
  }

  createGraph(inputs: InputCollections, _context: Context): GraphCollections {
    const orderedMetrics = inputs.metrics.map(OrderByTimestampMapper);
    return { metrics: orderedMetrics };
  }
}

export function service(): SkipService<InputCollections, GraphCollections> {
  return new Service();
}
